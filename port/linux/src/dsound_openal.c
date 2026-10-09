/*
DSOUND_OPENAL.C

Xbox DirectSound for OpenCE with OpenAL Soft backend.

Implements true 3D positional audio, HRTF spatialization for headphones,
directional audio cones, Doppler shift, and environmental reverb / occlusion
filtering via OpenAL EFX.

Audio data is decoded from Xbox ADPCM or 16-bit PCM and streamed via OpenAL
source buffer queues (alSourceQueueBuffers). Finished buffers are reclaimed in
DirectSoundDoWork on the main thread, keeping the game thread-safe without
concurrent callbacks.

If OpenAL Soft is unavailable or audio.enabled is false in config.toml, a silent
clock thread maintains packet progression so scripts, cutscenes and game logic
never freeze.
*/

#include "platform.h"
#include "port_config.h"
#include "sdl_platform.h"


#include <AL/al.h>
#include <AL/alc.h>
#include <AL/alext.h>
#include <AL/efx.h>
#include <SDL3/SDL.h>


#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>


#define MAXIMUM_STREAM_PACKETS 64
#define XBOX_ADPCM_BLOCK_BYTES 36
#define XBOX_ADPCM_BLOCK_SAMPLES 64

/* ---------- OpenAL dynamically loaded function pointers ---------- */

/* ALC functions */
static ALCdevice *(ALCAPIENTRY *palcOpenDevice)(const ALCchar *devicename);
static ALCboolean(ALCAPIENTRY *palcCloseDevice)(ALCdevice *device);
static ALCcontext *(ALCAPIENTRY *palcCreateContext)(ALCdevice *device,
                                                    const ALCint *attrlist);
static ALCboolean(ALCAPIENTRY *palcMakeContextCurrent)(ALCcontext *context);
static void(ALCAPIENTRY *palcDestroyContext)(ALCcontext *context);
static ALCdevice *(ALCAPIENTRY *palcGetContextsDevice)(ALCcontext *context);
static ALCboolean(ALCAPIENTRY *palcIsExtensionPresent)(ALCdevice *device,
                                                       const ALCchar *extname);
static void *(ALCAPIENTRY *palcGetProcAddress)(ALCdevice *device,
                                               const ALCchar *funcname);
static ALCenum(ALCAPIENTRY *palcGetError)(ALCdevice *device);
static const ALCchar *(ALCAPIENTRY *palcGetString)(ALCdevice *device,
                                                   ALCenum param);
static void(ALCAPIENTRY *palcGetIntegerv)(ALCdevice *device, ALCenum param,
                                          ALCsizei size, ALCint *values);

/* AL core functions */
static void(ALAPIENTRY *palGenSources)(ALsizei n, ALuint *sources);
static void(ALAPIENTRY *palDeleteSources)(ALsizei n, const ALuint *sources);
static ALboolean(ALAPIENTRY *palIsSource)(ALuint source);
static void(ALAPIENTRY *palSourcef)(ALuint source, ALenum param, ALfloat value);
static void(ALAPIENTRY *palSource3f)(ALuint source, ALenum param, ALfloat v1,
                                     ALfloat v2, ALfloat v3);
static void(ALAPIENTRY *palSourcefv)(ALuint source, ALenum param,
                                     const ALfloat *values);
static void(ALAPIENTRY *palSourcei)(ALuint source, ALenum param, ALint value);
static void(ALAPIENTRY *palSource3i)(ALuint source, ALenum param, ALint v1,
                                     ALint v2, ALint v3);
static void(ALAPIENTRY *palSourceiv)(ALuint source, ALenum param,
                                     const ALint *values);
static void(ALAPIENTRY *palGetSourcef)(ALuint source, ALenum param,
                                       ALfloat *value);
static void(ALAPIENTRY *palGetSourcei)(ALuint source, ALenum param,
                                       ALint *value);
static void(ALAPIENTRY *palSourcePlay)(ALuint source);
static void(ALAPIENTRY *palSourcePause)(ALuint source);
static void(ALAPIENTRY *palSourceStop)(ALuint source);
static void(ALAPIENTRY *palSourceRewind)(ALuint source);
static void(ALAPIENTRY *palSourceQueueBuffers)(ALuint source, ALsizei nb,
                                               const ALuint *buffers);
static void(ALAPIENTRY *palSourceUnqueueBuffers)(ALuint source, ALsizei nb,
                                                 ALuint *buffers);
static void(ALAPIENTRY *palGenBuffers)(ALsizei n, ALuint *buffers);
static void(ALAPIENTRY *palDeleteBuffers)(ALsizei n, const ALuint *buffers);
static ALboolean(ALAPIENTRY *palIsBuffer)(ALuint buffer);
static void(ALAPIENTRY *palBufferData)(ALuint buffer, ALenum format,
                                       const ALvoid *data, ALsizei size,
                                       ALsizei freq);
static void(ALAPIENTRY *palListenerf)(ALenum param, ALfloat value);
static void(ALAPIENTRY *palListener3f)(ALenum param, ALfloat v1, ALfloat v2,
                                       ALfloat v3);
static void(ALAPIENTRY *palListenerfv)(ALenum param, const ALfloat *values);
static void(ALAPIENTRY *palGetListenerf)(ALenum param, ALfloat *value);
static void(ALAPIENTRY *palDistanceModel)(ALenum distanceModel);
static void(ALAPIENTRY *palDopplerFactor)(ALfloat dopplerFactor);
static void(ALAPIENTRY *palSpeedOfSound)(ALfloat speed);
static ALenum(ALAPIENTRY *palGetError)(void);
static ALboolean(ALAPIENTRY *palIsExtensionPresent)(const ALchar *extname);
static void *(ALAPIENTRY *palGetProcAddress)(const ALchar *fname);

/* EFX functions */
static LPALGENEFFECTS palGenEffects;
static LPALDELETEEFFECTS palDeleteEffects;
static LPALEFFECTI palEffecti;
static LPALEFFECTF palEffectf;
static LPALGENFILTERS palGenFilters;
static LPALDELETEFILTERS palDeleteFilters;
static LPALFILTERI palFilteri;
static LPALFILTERF palFilterf;
static LPALGENAUXILIARYEFFECTSLOTS palGenAuxiliaryEffectSlots;
static LPALDELETEAUXILIARYEFFECTSLOTS palDeleteAuxiliaryEffectSlots;
static LPALAUXILIARYEFFECTSLOTI palAuxiliaryEffectSloti;

static void *al_shared_lib = NULL;
static ALCdevice *al_device = NULL;
static ALCcontext *al_context = NULL;
static boolean al_active = FALSE;
static boolean has_efx = FALSE;
static boolean has_source_spatialize = FALSE;
static boolean has_direct_channels = FALSE;
static ALuint global_reverb_effect = 0;
static ALuint global_reverb_slot = 0;

static float mix_bin_headroom = 1.0f;

/* ---------- Voice and Stream Structures ---------- */

struct voice_packet {
  XMEDIAPACKET packet;
  ALuint buffer;  /* OpenAL buffer holding decoded PCM data */
  short *samples; /* Interleaved 16-bit PCM samples */
  unsigned long frames;
  BOOL finished; /* Completed by mixer / clock thread */
};

struct al_stream {
  /* Must be first: in C an IDirectSoundStream is { lpVtbl } */
  IDirectSoundStream object;
  struct al_stream *next;
  ULONG reference_count;
  LPFNXMEDIAOBJECTCALLBACK callback;
  LPVOID context;

  /* Format */
  BOOL adpcm;
  unsigned long channels;
  DWORD sample_rate;
  DWORD frequency;

  BOOL paused;

  /* ADPCM state */
  unsigned char residual_adpcm[72];
  unsigned long residual_bytes;

  /* OpenAL handles */
  ALuint source;
  ALuint direct_filter; /* Low-pass filter for obstruction / occlusion */
  BOOL has_direct_filter;
  float filter_gain;
  float filter_gain_hf;
  BOOL filter_dirty;
  BOOL dirty;

  /* 2D mixing */
  float volume;
  float mix_left, mix_right;

  /* 3D attributes */
  BOOL stereo_positioned;
  float stereo_pan;
  float stereo_distance_fade;
  BOOL has_3d;
  DWORD mode;
  float position[3];
  float velocity[3];
  float minimum_distance, maximum_distance;
  float i3dl2_gain;
  float doppler_pitch;
  uint64_t last_doppler_time;

  /* Cones */
  DWORD cone_inside, cone_outside;
  float cone_orientation[3];
  LONG cone_outside_volume;

  /* Packet queue */
  struct voice_packet packets[MAXIMUM_STREAM_PACKETS];
  unsigned long packet_head;
  unsigned long packet_count;

  /* Fallback clock cursor (in source frames) */
  double cursor;
};

static pthread_mutex_t stream_lock = PTHREAD_MUTEX_INITIALIZER;
static struct al_stream *streams = NULL;

/* Listener in DirectSound space (+x right, +y up, +z forward) */
static struct {
  float position[3];
  float velocity[3];
  float front[3];
  float top[3];
  float rolloff_factor;
  float distance_factor;
  BOOL dirty_pos;
  BOOL dirty_vel;
  BOOL dirty_ori;
} listener = {{0, 0, 0}, {0, 0, 0}, {0, 0, 1}, {0, 1, 0}, 1.0f,
              1.0f,      FALSE,     FALSE,     FALSE};

static DSI3DL2LISTENER cached_i3dl2_listener;
static BOOL i3dl2_listener_dirty = FALSE;

static void apply_i3dl2_listener_locked(const DSI3DL2LISTENER *props);

static float master_volume = 1.0f;

static float gain_from_millibels(LONG millibels) {
  if (millibels <= DSBVOLUME_MIN)
    return 0.0f;
  return powf(10.0f, (float)millibels / 2000.0f);
}

static inline float clampf(float val, float min, float max) {
  if (val < min)
    return min;
  if (val > max)
    return max;
  return val;
}

static float doppler_factor = 1.0f;

static float compute_doppler_pitch(const struct al_stream *s) {
  if (doppler_factor <= 0.0f || !s->has_3d || s->mode == DS3DMODE_DISABLE)
    return 1.0f;

  float c = 343.3f / (listener.distance_factor > 0.0f
                          ? listener.distance_factor : 1.0f);
  float lp[3] = {0}, lv[3] = {0};
  if (s->mode != DS3DMODE_HEADRELATIVE) {
    memcpy(lp, listener.position, sizeof(lp));
    memcpy(lv, listener.velocity, sizeof(lv));
  }

  float rel[3] = { s->position[0]-lp[0], s->position[1]-lp[1],
                   s->position[2]-lp[2] };
  float d = sqrtf(rel[0]*rel[0] + rel[1]*rel[1] + rel[2]*rel[2]);
  if (d < 1.0e-3f)
    return 1.0f;

  /* components along the listener -> source line */
  float vs = (s->velocity[0]*rel[0] + s->velocity[1]*rel[1] +
              s->velocity[2]*rel[2]) / d;
  float vl = (lv[0]*rel[0] + lv[1]*rel[1] + lv[2]*rel[2]) / d;

  vs = clampf(vs * doppler_factor, -0.99f * c, 10.0f * c);
  vl = clampf(vl * doppler_factor, -10.0f * c, 10.0f * c);

  /* source moving away (vs>0) => pitch drops; listener approaching => rises */
  float denom = fmaxf(c + vs, 0.01f * c);
  float ratio = (c + vl) / denom;
  return clampf(ratio, 0.5f, 2.0f);
}

static float smooth_doppler_pitch(float current, float target, float delta_time) {
  const float smoothing_time = 0.05f; /* 50 ms */
  float alpha = 1.0f - expf(-delta_time / smoothing_time);
  return current + (target - current) * alpha;
}

static void normalize3(float *vector) {
  float length = sqrtf(vector[0] * vector[0] + vector[1] * vector[1] +
                       vector[2] * vector[2]);
  if (length > 1.0e-6f) {
    vector[0] /= length;
    vector[1] /= length;
    vector[2] /= length;
  }
}

/* ---------- ADPCM and PCM Decoding ---------- */

static const int ima_index_table[16] = {
    -1, -1, -1, -1, 2, 4, 6, 8, -1, -1, -1, -1, 2, 4, 6, 8,
};

static const int ima_step_table[89] = {
    7,     8,     9,     10,    11,    12,    13,    14,    16,    17,
    19,    21,    23,    25,    28,    31,    34,    37,    41,    45,
    50,    55,    60,    66,    73,    80,    88,    97,    107,   118,
    130,   143,   157,   173,   190,   209,   230,   253,   279,   307,
    337,   371,   408,   449,   494,   544,   598,   658,   724,   796,
    876,   963,   1060,  1166,  1282,  1411,  1552,  1707,  1878,  2066,
    2272,  2499,  2749,  3024,  3327,  3660,  4026,  4428,  4871,  5358,
    5894,  6484,  7132,  7845,  8630,  9493,  10442, 11487, 12635, 13899,
    15289, 16818, 18500, 20350, 22385, 24623, 27086, 29794, 32767,
};

static int ima_expand(int nibble, int *predictor, int *index) {
  int step = ima_step_table[*index];
  int difference = step >> 3;

  if (nibble & 1)
    difference += step >> 2;
  if (nibble & 2)
    difference += step >> 1;
  if (nibble & 4)
    difference += step;
  if (nibble & 8)
    difference = -difference;
  *predictor += difference;
  if (*predictor > 32767)
    *predictor = 32767;
  if (*predictor < -32768)
    *predictor = -32768;
  *index += ima_index_table[nibble];
  if (*index < 0)
    *index = 0;
  if (*index > 88)
    *index = 88;
  return *predictor;
}

static short *decode_adpcm(const unsigned char *source, unsigned long size,
                           unsigned long channels, unsigned long *frame_count) {
  unsigned long block_bytes = XBOX_ADPCM_BLOCK_BYTES * channels;
  unsigned long blocks = size / block_bytes;
  short *samples = malloc((blocks ? blocks : 1) * XBOX_ADPCM_BLOCK_SAMPLES *
                          channels * sizeof(short));
  unsigned long block, channel;

  if (!samples) {
    *frame_count = 0;
    return NULL;
  }
  for (block = 0; block < blocks; block++) {
    const unsigned char *data = source + block * block_bytes;
    short *output = samples + block * XBOX_ADPCM_BLOCK_SAMPLES * channels;

    for (channel = 0; channel < channels; channel++) {
      const unsigned char *header = data + channel * 4;
      int predictor = (short)(header[0] | (header[1] << 8));
      int index = header[2] > 88 ? 88 : header[2];
      unsigned long group, byte;

      for (group = 0; group < 8; group++) {
        const unsigned char *nibbles =
            data + 4 * channels + (group * channels + channel) * 4;

        for (byte = 0; byte < 4; byte++) {
          unsigned long sample = group * 8 + byte * 2;

          output[sample * channels + channel] =
              (short)ima_expand(nibbles[byte] & 0xf, &predictor, &index);
          output[(sample + 1) * channels + channel] =
              (short)ima_expand(nibbles[byte] >> 4, &predictor, &index);
        }
      }
    }
  }
  *frame_count = blocks * XBOX_ADPCM_BLOCK_SAMPLES;
  return samples;
}

static short *decode_pcm(const unsigned char *source, unsigned long size,
                         unsigned long channels, unsigned long *frame_count) {
  unsigned long frames = size / (2 * channels);
  short *samples = malloc((frames ? frames : 1) * channels * sizeof(short));

  if (samples)
    memcpy(samples, source, frames * channels * sizeof(short));
  *frame_count = samples ? frames : 0;
  return samples;
}

/* ---------- Source Updates ---------- */

static void update_source_properties(struct al_stream *stream) {
  if (!al_active || !stream->source)
    return;

  /* Pitch */
  if (stream->sample_rate > 0) {
    float pitch =
        (float)(stream->frequency ? stream->frequency : stream->sample_rate) /
        (float)stream->sample_rate;

    float target = compute_doppler_pitch(stream);
    
    uint64_t current_time = SDL_GetTicks();
    float delta_time = (stream->last_doppler_time == 0) ? 0.0f : (current_time - stream->last_doppler_time) / 1000.0f;
    stream->last_doppler_time = current_time;

    stream->doppler_pitch = smooth_doppler_pitch(stream->doppler_pitch, target, delta_time);

    pitch *= stream->doppler_pitch;
    pitch = clampf(pitch, 0.5f, 2.0f);
    palSourcef(stream->source, AL_PITCH, pitch);
  }

  /* 3D vs 2D */
  if (stream->has_3d && stream->mode != DS3DMODE_DISABLE) {
    if (has_source_spatialize)
      palSourcei(stream->source, AL_SOURCE_SPATIALIZE_SOFT, AL_TRUE);
    if (has_direct_channels)
      palSourcei(stream->source, AL_DIRECT_CHANNELS_SOFT, AL_FALSE);

    palSourcei(stream->source, AL_SOURCE_RELATIVE,
               (stream->mode == DS3DMODE_HEADRELATIVE) ? AL_TRUE : AL_FALSE);
    /* Convert DirectSound LH (+Z fwd) to OpenAL RH (-Z fwd) */
    palSource3f(stream->source, AL_POSITION, stream->position[0],
                stream->position[1], -stream->position[2]);
    palSource3f(stream->source, AL_VELOCITY, stream->velocity[0],
                stream->velocity[1], -stream->velocity[2]);
    palSourcef(stream->source, AL_REFERENCE_DISTANCE,
               stream->minimum_distance > 0.0f ? stream->minimum_distance
                                               : 1.0f);
    palSourcef(stream->source, AL_MAX_DISTANCE,
               stream->maximum_distance > stream->minimum_distance
                   ? stream->maximum_distance
                   : 1000.0f);
    palSourcef(stream->source, AL_ROLLOFF_FACTOR, listener.rolloff_factor);
    palSourcef(stream->source, AL_GAIN,
               stream->volume * stream->i3dl2_gain * mix_bin_headroom);

    /* Directional cones */
    if (stream->cone_inside < 360 || stream->cone_outside < 360) {
      palSourcef(stream->source, AL_CONE_INNER_ANGLE,
                 (float)stream->cone_inside);
      palSourcef(stream->source, AL_CONE_OUTER_ANGLE,
                 (float)stream->cone_outside);
      palSource3f(stream->source, AL_DIRECTION, stream->cone_orientation[0],
                  stream->cone_orientation[1], -stream->cone_orientation[2]);
      palSourcef(
          stream->source, AL_CONE_OUTER_GAIN,
          clampf(gain_from_millibels(stream->cone_outside_volume), 0.0f, 1.0f));
    } else {
      palSourcef(stream->source, AL_CONE_INNER_ANGLE, 360.0f);
      palSourcef(stream->source, AL_CONE_OUTER_ANGLE, 360.0f);
    }
  } else {
    /* 2D voice: do not apply HRTF spatialization to non-diegetic sounds (UI,
     * HUD, dialogue) */
    if (has_source_spatialize)
      palSourcei(stream->source, AL_SOURCE_SPATIALIZE_SOFT, AL_TRUE);

    palSourcei(stream->source, AL_SOURCE_RELATIVE, AL_TRUE);
    palSourcef(stream->source, AL_ROLLOFF_FACTOR, 0.0f);

    if (stream->channels == 1) {
      if (has_direct_channels)
        palSourcei(stream->source, AL_DIRECT_CHANNELS_SOFT, AL_FALSE);

      /* Pan mono voices across left/right bins */
      float total = stream->mix_left + stream->mix_right;
      float pan = total > 1.0e-4f
                      ? (stream->mix_right - stream->mix_left) / total
                      : 0.0f;
      float gain = fmaxf(stream->mix_left, stream->mix_right) * stream->volume *
                   mix_bin_headroom;
      palSource3f(stream->source, AL_POSITION, pan, 0.0f,
                  -sqrtf(fmaxf(0.0f, 1.0f - pan * pan)));
      palSourcef(stream->source, AL_GAIN, gain);
    } else {
      /* Stereo voices (music, cutscenes) pass through directly without
       * crossfeed or downmixing unless positioned */
      if (has_direct_channels)
        palSourcei(stream->source, AL_DIRECT_CHANNELS_SOFT, stream->stereo_positioned ? AL_FALSE : AL_TRUE);

      float gain = stream->volume * mix_bin_headroom;
      if (stream->stereo_positioned) {
        gain *= stream->stereo_distance_fade * stream->i3dl2_gain;
        palSource3f(stream->source, AL_POSITION, stream->stereo_pan, 0.0f,
                    -sqrtf(fmaxf(0.0f, 1.0f - stream->stereo_pan * stream->stereo_pan)));
      } else {
        palSource3f(stream->source, AL_POSITION, 0.0f, 0.0f, 0.0f);
      }
      palSourcef(stream->source, AL_GAIN, gain);
    }
  }

  /* EFX direct low-pass filter for obstruction / occlusion */
  if (has_efx && stream->filter_dirty) {
    if (!stream->has_direct_filter) {
      palGenFilters(1, &stream->direct_filter);
      palFilteri(stream->direct_filter, AL_FILTER_TYPE, AL_FILTER_LOWPASS);
      stream->has_direct_filter = TRUE;
    }
    palFilterf(stream->direct_filter, AL_LOWPASS_GAIN, stream->filter_gain);
    palFilterf(stream->direct_filter, AL_LOWPASS_GAINHF,
               stream->filter_gain_hf);
    palSourcei(stream->source, AL_DIRECT_FILTER, stream->direct_filter);
    stream->filter_dirty = FALSE;
  }
}

/* ---------- Completion ---------- */

static void stream_complete_head(struct al_stream *stream, DWORD status,
                                 DWORD completed_size) {
  struct voice_packet *entry = &stream->packets[stream->packet_head];
  XMEDIAPACKET packet = entry->packet;

  if (al_active && entry->buffer) {
    palDeleteBuffers(1, &entry->buffer);
    entry->buffer = 0;
  }
  free(entry->samples);
  entry->samples = NULL;
  entry->finished = FALSE;

  stream->packet_head = (stream->packet_head + 1) % MAXIMUM_STREAM_PACKETS;
  stream->packet_count--;

  if (packet.pdwCompletedSize)
    *packet.pdwCompletedSize = completed_size;
  if (packet.pdwStatus)
    *packet.pdwStatus = status;

  if (stream->callback) {
    pthread_mutex_unlock(&stream_lock);
    stream->callback(stream->context, packet.pContext, status);
    pthread_mutex_lock(&stream_lock);
  } else if (packet.hCompletionEvent) {
    SetEvent(packet.hCompletionEvent);
  }
}

/* ---------- Silent Clock Thread Fallback ---------- */

static void *silent_clock_thread(void *argument) {
  (void)argument;
  while (1) {
    SDL_Delay(10);

    pthread_mutex_lock(&stream_lock);
    for (struct al_stream *stream = streams; stream; stream = stream->next) {
      if (stream->paused || !stream->packet_count || !stream->sample_rate)
        continue;

      double step = (double)(stream->frequency ? stream->frequency
                                               : stream->sample_rate) *
                    0.01;
      stream->cursor += step;

      /* Find the finished packets sequentially. Do not scan from the beginning each time. */
      unsigned long i = 0;
      while (i < stream->packet_count) {
        struct voice_packet *packet = &stream->packets[(stream->packet_head + i) %
                                                       MAXIMUM_STREAM_PACKETS];
        if (!packet->finished) {
          if (stream->cursor >= (double)packet->frames) {
            stream->cursor -= (double)packet->frames;
            packet->finished = TRUE;
          } else {
            /* Stop the search. This packet is not finished. */
            break;
          }
        }
        i++;
      }
    }
    pthread_mutex_unlock(&stream_lock);
  }
  return NULL;
}

/* ---------- OpenAL Dynamic Loading and Initialization ---------- */

static boolean al_load(void) {
  static const char *candidates[] = {
      "soft_oal.dll",    "OpenAL32.dll",
      "libopenal.so.1",  "libopenal.so",
      "libopenal.dylib", "/System/Library/Frameworks/OpenAL.framework/OpenAL"};

  const char *base_path = SDL_GetBasePath();
  char path_buf[512];

  /* Step 1: Check executable directory */
  if (base_path) {
    for (size_t i = 0; i < sizeof(candidates) / sizeof(candidates[0]); i++) {
      snprintf(path_buf, sizeof(path_buf), "%s%s", base_path, candidates[i]);
      al_shared_lib = SDL_LoadObject(path_buf);
      if (al_shared_lib) {
        platform_log("OpenAL: loaded %s", path_buf);
        break;
      }
    }
  }

  /* Step 2: Check standard system library search path */
  if (!al_shared_lib) {
    for (size_t i = 0; i < sizeof(candidates) / sizeof(candidates[0]); i++) {
      al_shared_lib = SDL_LoadObject(candidates[i]);
      if (al_shared_lib) {
        platform_log("OpenAL: loaded system %s", candidates[i]);
        break;
      }
    }
  }

  if (!al_shared_lib) {
    platform_log("OpenAL: library not found; using silent audio fallback");
    return FALSE;
  }

#define LOAD_ALC(name)                                                         \
  do {                                                                         \
    palc##name = (void *)SDL_LoadFunction(al_shared_lib, "alc" #name);         \
    if (!palc##name) {                                                         \
      platform_log("OpenAL: missing alc" #name);                               \
      return FALSE;                                                            \
    }                                                                          \
  } while (0)

#define LOAD_AL(name)                                                          \
  do {                                                                         \
    pal##name = (void *)SDL_LoadFunction(al_shared_lib, "al" #name);           \
    if (!pal##name) {                                                          \
      platform_log("OpenAL: missing al" #name);                                \
      return FALSE;                                                            \
    }                                                                          \
  } while (0)

  LOAD_ALC(OpenDevice);
  LOAD_ALC(CloseDevice);
  LOAD_ALC(CreateContext);
  LOAD_ALC(MakeContextCurrent);
  LOAD_ALC(DestroyContext);
  LOAD_ALC(GetContextsDevice);
  LOAD_ALC(IsExtensionPresent);
  LOAD_ALC(GetProcAddress);
  LOAD_ALC(GetError);
  LOAD_ALC(GetString);
  LOAD_ALC(GetIntegerv);

  LOAD_AL(GenSources);
  LOAD_AL(DeleteSources);
  LOAD_AL(IsSource);
  LOAD_AL(Sourcef);
  LOAD_AL(Source3f);
  LOAD_AL(Sourcefv);
  LOAD_AL(Sourcei);
  LOAD_AL(Source3i);
  LOAD_AL(Sourceiv);
  LOAD_AL(GetSourcef);
  LOAD_AL(GetSourcei);
  LOAD_AL(SourcePlay);
  LOAD_AL(SourcePause);
  LOAD_AL(SourceStop);
  LOAD_AL(SourceRewind);
  LOAD_AL(SourceQueueBuffers);
  LOAD_AL(SourceUnqueueBuffers);
  LOAD_AL(GenBuffers);
  LOAD_AL(DeleteBuffers);
  LOAD_AL(IsBuffer);
  LOAD_AL(BufferData);
  LOAD_AL(Listenerf);
  LOAD_AL(Listener3f);
  LOAD_AL(Listenerfv);
  LOAD_AL(GetListenerf);
  LOAD_AL(DistanceModel);
  LOAD_AL(DopplerFactor);
  LOAD_AL(SpeedOfSound);
  LOAD_AL(GetError);
  LOAD_AL(IsExtensionPresent);
  LOAD_AL(GetProcAddress);

#undef LOAD_ALC
#undef LOAD_AL

  return TRUE;
}

static void audio_start(void) {
  static boolean started = FALSE;
  if (started)
    return;
  started = TRUE;

  master_volume = (float)config_real("audio.volume");

  if (!config_boolean("audio.enabled")) {
    platform_log("audio.enabled is false: starting silent clock fallback");
    pthread_t thread;
    pthread_create(&thread, NULL, silent_clock_thread, NULL);
    pthread_detach(thread);
    return;
  }

  if (!al_load()) {
    pthread_t thread;
    pthread_create(&thread, NULL, silent_clock_thread, NULL);
    pthread_detach(thread);
    return;
  }

  al_device = palcOpenDevice(NULL);
  if (!al_device) {
    platform_log("OpenAL: failed to open default audio device");
    pthread_t thread;
    pthread_create(&thread, NULL, silent_clock_thread, NULL);
    pthread_detach(thread);
    return;
  }

#define MASTER_HEADROOM 0.5f

#ifndef ALC_OUTPUT_LIMITER_SOFT
#define ALC_OUTPUT_LIMITER_SOFT 0x199A
#endif

  ALCint attrlist[] = { ALC_OUTPUT_LIMITER_SOFT, ALC_TRUE, 0 };
  al_context = palcCreateContext(al_device, attrlist);
  if (!al_context) {
    platform_log("OpenAL: failed to create context");
    palcCloseDevice(al_device);
    al_device = NULL;
    pthread_t thread;
    pthread_create(&thread, NULL, silent_clock_thread, NULL);
    pthread_detach(thread);
    return;
  }

  palcMakeContextCurrent(al_context);
  al_active = TRUE;

  /* Log HRTF status from OpenAL Soft configuration (alsoft.ini) */
  if (palcIsExtensionPresent(al_device, "ALC_SOFT_HRTF")) {
    ALCint hrtf_status = 0;
    palcGetIntegerv(al_device, ALC_HRTF_STATUS_SOFT, 1, &hrtf_status);
    const char *status_str = "unknown";
    switch (hrtf_status) {
    case ALC_HRTF_DISABLED_SOFT:
      status_str = "disabled";
      break;
    case ALC_HRTF_ENABLED_SOFT:
      status_str = "enabled";
      break;
    case ALC_HRTF_DENIED_SOFT:
      status_str = "denied";
      break;
    case ALC_HRTF_REQUIRED_SOFT:
      status_str = "required";
      break;
    case ALC_HRTF_HEADPHONES_DETECTED_SOFT:
      status_str = "headphones detected";
      break;
    case ALC_HRTF_UNSUPPORTED_FORMAT_SOFT:
      status_str = "unsupported format";
      break;
    }
    const char *specifier = palcGetString(al_device, ALC_HRTF_SPECIFIER_SOFT);
    platform_log("OpenAL Soft HRTF: status=%s (%d)%s%s", status_str,
                 hrtf_status, specifier ? ", specifier=" : "",
                 specifier ? specifier : "");
  }

  has_source_spatialize = palIsExtensionPresent("AL_SOFT_source_spatialize");
  has_direct_channels = palIsExtensionPresent("AL_SOFT_direct_channels");
  if (has_source_spatialize)
    platform_log("OpenAL Soft: AL_SOFT_source_spatialize supported");
  if (has_direct_channels)
    platform_log("OpenAL Soft: AL_SOFT_direct_channels supported");

  /* Distance model matching DirectSound inverse distance with max clamp */
  palDistanceModel(AL_INVERSE_DISTANCE_CLAMPED);
  palDopplerFactor(0.0f);
  palSpeedOfSound(343.3f / (listener.distance_factor > 0.0f
                                ? listener.distance_factor
                                : 1.0f));
  palListenerf(AL_GAIN, master_volume * MASTER_HEADROOM);

  /* Check EFX extension for environmental reverb and obstruction/occlusion
   * filters */
  if (palcIsExtensionPresent(al_device, "ALC_EXT_EFX")) {
    palGenEffects = (LPALGENEFFECTS)palGetProcAddress("alGenEffects");
    palDeleteEffects = (LPALDELETEEFFECTS)palGetProcAddress("alDeleteEffects");
    palEffecti = (LPALEFFECTI)palGetProcAddress("alEffecti");
    palEffectf = (LPALEFFECTF)palGetProcAddress("alEffectf");
    palGenFilters = (LPALGENFILTERS)palGetProcAddress("alGenFilters");
    palDeleteFilters = (LPALDELETEFILTERS)palGetProcAddress("alDeleteFilters");
    palFilteri = (LPALFILTERI)palGetProcAddress("alFilteri");
    palFilterf = (LPALFILTERF)palGetProcAddress("alFilterf");
    palGenAuxiliaryEffectSlots = (LPALGENAUXILIARYEFFECTSLOTS)palGetProcAddress(
        "alGenAuxiliaryEffectSlots");
    palDeleteAuxiliaryEffectSlots =
        (LPALDELETEAUXILIARYEFFECTSLOTS)palGetProcAddress(
            "alDeleteAuxiliaryEffectSlots");
    palAuxiliaryEffectSloti =
        (LPALAUXILIARYEFFECTSLOTI)palGetProcAddress("alAuxiliaryEffectSloti");

    if (palGenEffects && palGenFilters && palGenAuxiliaryEffectSlots) {
      has_efx = TRUE;
      palGenEffects(1, &global_reverb_effect);
      palEffecti(global_reverb_effect, AL_EFFECT_TYPE, AL_EFFECT_REVERB);
      palGenAuxiliaryEffectSlots(1, &global_reverb_slot);
      palAuxiliaryEffectSloti(global_reverb_slot, AL_EFFECTSLOT_EFFECT,
                              global_reverb_effect);
      platform_log("OpenAL EFX: environmental reverb and filters initialized");
    }
  }
}

/* ---------- Stream Media Object Implementation ---------- */

static struct al_stream *stream_from_interface(void *stream) {
  return (struct al_stream *)stream;
}

static ULONG STDMETHODCALLTYPE
stream_add_reference(IDirectSoundStream *object) {
  struct al_stream *stream = stream_from_interface(object);
  pthread_mutex_lock(&stream_lock);
  ULONG count = ++stream->reference_count;
  pthread_mutex_unlock(&stream_lock);
  return count;
}

static HRESULT STDMETHODCALLTYPE stream_flush(IDirectSoundStream *object);

static ULONG STDMETHODCALLTYPE stream_release(IDirectSoundStream *object) {
  struct al_stream *stream = stream_from_interface(object);
  struct al_stream **link;
  ULONG count;

  pthread_mutex_lock(&stream_lock);
  if (stream->reference_count > 0)
    stream->reference_count--;
  count = stream->reference_count;

  if (count > 0) {
    pthread_mutex_unlock(&stream_lock);
    return count;
  }

  /* Before we free it, we MUST flush it. We temporarily increment refcount to
   * prevent recursive frees. */
  stream->reference_count = 1;

  if (al_active && stream->source) {
    palSourceStop(stream->source);
    palSourcei(stream->source, AL_BUFFER, 0);
  }

  while (stream->packet_count > 0) {
    stream_complete_head(stream, XMEDIAPACKET_STATUS_FLUSHED, 0);
  }

  /* Check if the callback resurrected the stream */
  stream->reference_count--;
  if (stream->reference_count > 0) {
    pthread_mutex_unlock(&stream_lock);
    return stream->reference_count;
  }

  if (al_active && stream->source) {
    palSourceStop(stream->source);
    if (has_efx) {
      if (stream->has_direct_filter) {
        palSourcei(stream->source, AL_DIRECT_FILTER, AL_FILTER_NULL);
        palDeleteFilters(1, &stream->direct_filter);
        stream->has_direct_filter = FALSE;
      }
      if (stream->has_3d && global_reverb_slot) {
        palSource3i(stream->source, AL_AUXILIARY_SEND_FILTER,
                    AL_EFFECTSLOT_NULL, 0, AL_FILTER_NULL);
      }
    }
    palDeleteSources(1, &stream->source);
    stream->source = 0;
  }

  for (link = &streams; *link; link = &(*link)->next) {
    if (*link == stream) {
      *link = stream->next;
      break;
    }
  }
  pthread_mutex_unlock(&stream_lock);
  free(stream);
  return 0;
}

static HRESULT STDMETHODCALLTYPE stream_flush(IDirectSoundStream *object) {
  struct al_stream *stream = stream_from_interface(object);

  pthread_mutex_lock(&stream_lock);
  stream->reference_count++;

  if (al_active && stream->source) {
    palSourceStop(stream->source);
    palSourcei(stream->source, AL_BUFFER, 0);
  }

  while (stream->packet_count > 0) {
    stream_complete_head(stream, XMEDIAPACKET_STATUS_FLUSHED, 0);
  }

  stream->cursor = 0.0;
  stream->residual_bytes = 0;
  pthread_mutex_unlock(&stream_lock);

  stream_release(object);
  return DS_OK;
}

static HRESULT STDMETHODCALLTYPE stream_get_info(IDirectSoundStream *object,
                                                 LPXMEDIAINFO information) {
  struct al_stream *stream = stream_from_interface(object);
  memset(information, 0, sizeof(*information));
  information->dwFlags =
      XMO_STREAMF_FIXED_SAMPLE_SIZE | XMO_STREAMF_INPUT_ASYNC;
  information->dwInputSize = stream->adpcm
                                 ? XBOX_ADPCM_BLOCK_BYTES * stream->channels
                                 : 2 * stream->channels;
  return S_OK;
}

static HRESULT STDMETHODCALLTYPE stream_get_status(IDirectSoundStream *object,
                                                   LPDWORD status) {
  struct al_stream *stream = stream_from_interface(object);
  pthread_mutex_lock(&stream_lock);
  *status = stream->packet_count < MAXIMUM_STREAM_PACKETS
                ? XMO_STATUSF_ACCEPT_INPUT_DATA
                : 0;
  pthread_mutex_unlock(&stream_lock);
  return S_OK;
}

static HRESULT STDMETHODCALLTYPE stream_process(IDirectSoundStream *object,
                                                LPCXMEDIAPACKET input,
                                                LPCXMEDIAPACKET output) {
  struct al_stream *stream = stream_from_interface(object);
  struct voice_packet *entry;
  unsigned long frames = 0;
  short *samples;
  ALuint al_buffer = 0;

  (void)output;
  if (!input)
    return E_INVALIDARG;

  if (stream->adpcm) {
    unsigned long block_bytes = XBOX_ADPCM_BLOCK_BYTES * stream->channels;
    if (input->dwMaxSize % block_bytes != 0)
      platform_log(
          "OpenAL: ADPCM dwMaxSize %lu is not a multiple of block_bytes %lu!",
          input->dwMaxSize, block_bytes);

    unsigned long total_bytes = stream->residual_bytes + input->dwMaxSize;
    unsigned long blocks = total_bytes / block_bytes;
    unsigned long decode_bytes = blocks * block_bytes;

    if (decode_bytes > 0) {
      unsigned char *combined = malloc(decode_bytes);
      if (stream->residual_bytes > 0)
        memcpy(combined, stream->residual_adpcm, stream->residual_bytes);

      unsigned long from_input = decode_bytes - stream->residual_bytes;
      memcpy(combined + stream->residual_bytes, input->pvBuffer, from_input);

      samples = decode_adpcm(combined, decode_bytes, stream->channels, &frames);
      free(combined);

      stream->residual_bytes = input->dwMaxSize - from_input;
      if (stream->residual_bytes > 0)
        memcpy(stream->residual_adpcm,
               (const unsigned char *)input->pvBuffer + from_input,
               stream->residual_bytes);
    } else {
      memcpy(stream->residual_adpcm + stream->residual_bytes, input->pvBuffer,
             input->dwMaxSize);
      stream->residual_bytes += input->dwMaxSize;
      samples = NULL;
      frames = 0;
    }
  } else {
    samples = decode_pcm(input->pvBuffer, input->dwMaxSize, stream->channels,
                         &frames);
  }

  pthread_mutex_lock(&stream_lock);
  if (stream->packet_count == MAXIMUM_STREAM_PACKETS) {
    pthread_mutex_unlock(&stream_lock);
    free(samples);
    return E_OUTOFMEMORY;
  }

  if (al_active && stream->source && samples && frames > 0) {
    ALenum format =
        (stream->channels == 2) ? AL_FORMAT_STEREO16 : AL_FORMAT_MONO16;
    palGenBuffers(1, &al_buffer);
    palBufferData(al_buffer, format, samples,
                  frames * stream->channels * sizeof(short),
                  stream->sample_rate);
    palSourceQueueBuffers(stream->source, 1, &al_buffer);

    if (!stream->paused) {
      ALint state;
      palGetSourcei(stream->source, AL_SOURCE_STATE, &state);
      if (state != AL_PLAYING && stream->packet_count >= 1)
        palSourcePlay(stream->source);
    }
  }

  entry = &stream->packets[(stream->packet_head + stream->packet_count) %
                           MAXIMUM_STREAM_PACKETS];
  entry->packet = *input;
  entry->samples = samples;
  entry->frames = samples ? frames : 0;
  entry->buffer = al_buffer;
  entry->finished = FALSE;

  if (input->pdwStatus)
    *input->pdwStatus = XMEDIAPACKET_STATUS_PENDING;
  if (input->pdwCompletedSize)
    *input->pdwCompletedSize =
        input->dwMaxSize; /* Report full consumption to game */

  stream->packet_count++;
  pthread_mutex_unlock(&stream_lock);
  return S_OK;
}

static HRESULT STDMETHODCALLTYPE
stream_discontinuity(IDirectSoundStream *object) {
  (void)object;
  return S_OK;
}

static IDirectSoundStreamVtbl stream_vtable = {
    stream_add_reference, stream_release, stream_get_info,
    stream_get_status,    stream_process, stream_discontinuity,
    stream_flush,
};

/* ---------- DirectSound Object Implementation ---------- */

struct al_direct_sound {
  ULONG reference_count;
};

static struct al_direct_sound direct_sound = {0};

HRESULT WINAPI DirectSoundCreate(LPGUID device_id, LPDIRECTSOUND *result,
                                 LPUNKNOWN outer) {
  (void)device_id;
  (void)outer;
  audio_start();
  direct_sound.reference_count++;
  *result = (LPDIRECTSOUND)&direct_sound;
  return DS_OK;
}

ULONG WINAPI IDirectSound_Release(LPDIRECTSOUND sound) {
  (void)sound;
  if (direct_sound.reference_count > 0) {
    direct_sound.reference_count--;
    if (direct_sound.reference_count == 0 && al_active) {
      pthread_mutex_lock(&stream_lock);
      al_active = FALSE;
      if (has_efx) {
        if (global_reverb_slot) {
          palAuxiliaryEffectSloti(global_reverb_slot, AL_EFFECTSLOT_EFFECT,
                                  AL_EFFECT_NULL);
          if (palDeleteAuxiliaryEffectSlots)
            palDeleteAuxiliaryEffectSlots(1, &global_reverb_slot);
          global_reverb_slot = 0;
        }
        if (global_reverb_effect) {
          if (palDeleteEffects)
            palDeleteEffects(1, &global_reverb_effect);
          global_reverb_effect = 0;
        }
      }
      palcMakeContextCurrent(NULL);
      if (al_context) {
        palcDestroyContext(al_context);
        al_context = NULL;
      }
      if (al_device) {
        palcCloseDevice(al_device);
        al_device = NULL;
      }
      if (al_shared_lib) {
        SDL_UnloadObject(al_shared_lib);
        al_shared_lib = NULL;
      }
      pthread_mutex_unlock(&stream_lock);
    }
  }
  return direct_sound.reference_count;
}

VOID WINAPI DirectSoundDoWork(void) {
  static unsigned long volume_read_at = (unsigned long)-1;

  if (volume_read_at != config_changes()) {
    volume_read_at = config_changes();
    master_volume = clampf((float)config_real("audio.volume"), 0.0f, 1.0f);
    if (al_active)
      palListenerf(AL_GAIN, master_volume * MASTER_HEADROOM);
  }

  pthread_mutex_lock(&stream_lock);
  
  /* Apply the deferred listener properties to OpenAL. */
  if (al_active) {
    if (listener.dirty_pos) {
      palListener3f(AL_POSITION, listener.position[0], listener.position[1], -listener.position[2]);
      listener.dirty_pos = FALSE;
    }
    if (listener.dirty_vel) {
      palListener3f(AL_VELOCITY, listener.velocity[0], listener.velocity[1], -listener.velocity[2]);
      listener.dirty_vel = FALSE;
    }
    if (listener.dirty_ori) {
      ALfloat orientation[6] = {listener.front[0],  listener.front[1], -listener.front[2],
                                listener.top[0],    listener.top[1],   -listener.top[2]};
      palListenerfv(AL_ORIENTATION, orientation);
      listener.dirty_ori = FALSE;
    }
    if (i3dl2_listener_dirty) {
      apply_i3dl2_listener_locked(&cached_i3dl2_listener);
      i3dl2_listener_dirty = FALSE;
    }
  }

  struct al_stream *current = streams;
  while (current) {
    /* Apply the deferred stream properties. */
    if (al_active && current->dirty) {
      update_source_properties(current);
      current->dirty = FALSE;
    }

    BOOL did_work = FALSE;

    if (al_active && current->source) {
      /* Complete any packets that didn't have an OpenAL buffer queued */
      while (current->packet_count > 0 &&
             current->packets[current->packet_head].buffer == 0) {
        stream_complete_head(
            current, XMEDIAPACKET_STATUS_SUCCESS,
            current->packets[current->packet_head].packet.dwMaxSize);
        did_work = TRUE;
      }

      if (!did_work) {
        ALint processed = 0;
        palGetSourcei(current->source, AL_BUFFERS_PROCESSED, &processed);

        if (processed > 0 && current->packet_count > 0) {
          ALuint unqueued[MAXIMUM_STREAM_PACKETS];
          int to_unqueue = processed > current->packet_count
                               ? current->packet_count
                               : processed;
          palSourceUnqueueBuffers(current->source, to_unqueue, unqueued);
          for (int i = 0; i < to_unqueue; i++) {
            while (current->packet_count > 0 &&
                   current->packets[current->packet_head].buffer == 0) {
              stream_complete_head(
                  current, XMEDIAPACKET_STATUS_SUCCESS,
                  current->packets[current->packet_head].packet.dwMaxSize);
            }
            if (current->packet_count == 0)
              break;
            stream_complete_head(
                current, XMEDIAPACKET_STATUS_SUCCESS,
                current->packets[current->packet_head].packet.dwMaxSize);
          }
          did_work = TRUE;
        } else if (current->packet_count > 0 && !current->paused) {
          ALint state;
          palGetSourcei(current->source, AL_SOURCE_STATE, &state);
          if (state == AL_STOPPED)
            palSourcePlay(current->source);
        }
      }
    } else {
      if (current->packet_count &&
          current->packets[current->packet_head].finished) {
        stream_complete_head(
            current, XMEDIAPACKET_STATUS_SUCCESS,
            current->packets[current->packet_head].packet.dwMaxSize);
        did_work = TRUE;
      }
    }

    if (did_work) {
      /* stream_complete_head may have dropped the lock. Verify current still
       * exists. */
      struct al_stream *check;
      for (check = streams; check; check = check->next) {
        if (check == current)
          break;
      }
      if (!check) {
        /* The stream was deleted while the lock was dropped. Restart from head.
         */
        current = streams;
        continue;
      }
      /* If it still exists, we want to process it again in case it has more
         buffers, so we do NOT advance current->next yet. */
      continue;
    }

    current = current->next;
  }
  pthread_mutex_unlock(&stream_lock);
}

VOID WINAPI DirectSoundUseFullHRTF(void) {
  /* OpenAL Soft configuration is controlled via alsoft.ini; do not override
   * user config. */
}

HRESULT WINAPI IDirectSound_GetCaps(LPDIRECTSOUND sound, LPDSCAPS caps) {
  (void)sound;
  memset(caps, 0, sizeof(*caps));
  caps->dwFree2DBuffers = 256;
  caps->dwFree3DBuffers = 256;
  caps->dwFreeBufferSGEs = 2047;
  caps->dwMemoryAllocated = 0;
  return DS_OK;
}

HRESULT WINAPI IDirectSound_GetSpeakerConfig(LPDIRECTSOUND sound,
                                             LPDWORD speaker_config) {
  (void)sound;
  *speaker_config = DSSPEAKER_STEREO;
  return DS_OK;
}

HRESULT WINAPI IDirectSound_DownloadEffectsImage(
    LPDIRECTSOUND sound, LPCVOID image, DWORD image_size,
    LPCDSEFFECTIMAGELOC image_location,
    LPDSEFFECTIMAGEDESC *image_description) {
  (void)sound;
  (void)image;
  (void)image_size;
  (void)image_location;
  if (image_description)
    *image_description = NULL;
  return DS_OK;
}

static void apply_i3dl2_listener_locked(const DSI3DL2LISTENER *props) {
  if (al_active && has_efx && global_reverb_effect && global_reverb_slot) {
    palEffectf(global_reverb_effect, AL_REVERB_GAIN,
               clampf(gain_from_millibels(props->lRoom), 0.0f, 1.0f));
    palEffectf(global_reverb_effect, AL_REVERB_GAINHF,
               clampf(gain_from_millibels(props->lRoomHF), 0.0f, 1.0f));
    palEffectf(global_reverb_effect, AL_REVERB_ROOM_ROLLOFF_FACTOR,
               clampf(props->flRoomRolloffFactor, 0.0f, 10.0f));
    palEffectf(global_reverb_effect, AL_REVERB_DECAY_TIME,
               clampf(props->flDecayTime, 0.1f, 20.0f));
    palEffectf(global_reverb_effect, AL_REVERB_DECAY_HFRATIO,
               clampf(props->flDecayHFRatio, 0.1f, 2.0f));
    palEffectf(global_reverb_effect, AL_REVERB_REFLECTIONS_GAIN,
               clampf(gain_from_millibels(props->lReflections), 0.0f, 3.16f));
    palEffectf(global_reverb_effect, AL_REVERB_REFLECTIONS_DELAY,
               clampf(props->flReflectionsDelay, 0.0f, 0.3f));
    palEffectf(global_reverb_effect, AL_REVERB_LATE_REVERB_GAIN,
               clampf(gain_from_millibels(props->lReverb), 0.0f, 10.0f));
    palEffectf(global_reverb_effect, AL_REVERB_LATE_REVERB_DELAY,
               clampf(props->flReverbDelay, 0.0f, 0.1f));
    palEffectf(global_reverb_effect, AL_REVERB_DIFFUSION,
               clampf(props->flDiffusion / 100.0f, 0.0f, 1.0f));
    palEffectf(global_reverb_effect, AL_REVERB_DENSITY,
               clampf(props->flDensity / 100.0f, 0.0f, 1.0f));
    palAuxiliaryEffectSloti(global_reverb_slot, AL_EFFECTSLOT_EFFECT,
                            global_reverb_effect);
  }
}

HRESULT WINAPI IDirectSound_CommitDeferredSettings(LPDIRECTSOUND sound) {
  (void)sound;
  pthread_mutex_lock(&stream_lock);
  if (al_active) {
    if (listener.dirty_pos || listener.dirty_vel) {
      for (struct al_stream *s = streams; s; s = s->next)
        if (s->has_3d) s->dirty = TRUE;
    }
    if (listener.dirty_pos) {
      palListener3f(AL_POSITION, listener.position[0], listener.position[1],
                    -listener.position[2]);
      listener.dirty_pos = FALSE;
    }
    if (listener.dirty_vel) {
      palListener3f(AL_VELOCITY, listener.velocity[0], listener.velocity[1],
                    -listener.velocity[2]);
      listener.dirty_vel = FALSE;
    }
    if (listener.dirty_ori) {
      ALfloat orientation[6] = {listener.front[0],  listener.front[1],
                                -listener.front[2], listener.top[0],
                                listener.top[1],    -listener.top[2]};
      palListenerfv(AL_ORIENTATION, orientation);
      listener.dirty_ori = FALSE;
    }
    if (i3dl2_listener_dirty) {
      apply_i3dl2_listener_locked(&cached_i3dl2_listener);
      i3dl2_listener_dirty = FALSE;
    }
    for (struct al_stream *stream = streams; stream; stream = stream->next) {
      if (stream->dirty) {
        update_source_properties(stream);
        stream->dirty = FALSE;
      }
    }
  }
  pthread_mutex_unlock(&stream_lock);
  return DS_OK;
}

HRESULT WINAPI IDirectSound_SetMixBinHeadroom(LPDIRECTSOUND sound,
                                              DWORD mix_bin_mask,
                                              DWORD headroom) {
  (void)sound;
  (void)mix_bin_mask;
  /* Xbox DirectSound maps headroom as a bit shift: each unit is -6dB (divide by
   * 2). */
  float scalar = 1.0f;
  if (headroom <= 7)
    scalar = powf(0.5f, (float)headroom);

  pthread_mutex_lock(&stream_lock);
  mix_bin_headroom = scalar;
  for (struct al_stream *stream = streams; stream; stream = stream->next) {
    stream->dirty = TRUE;
  }
  pthread_mutex_unlock(&stream_lock);
  return DS_OK;
}

HRESULT WINAPI IDirectSound_SetI3DL2Listener(LPDIRECTSOUND sound,
                                             LPCDSI3DL2LISTENER props,
                                             DWORD apply) {
  (void)sound;
  if (!props)
    return DS_OK;

  pthread_mutex_lock(&stream_lock);
  if (memcmp(&cached_i3dl2_listener, props, sizeof(*props)) == 0) {
    pthread_mutex_unlock(&stream_lock);
    return DS_OK;
  }

  cached_i3dl2_listener = *props;
  if (apply == DS3D_DEFERRED) {
    i3dl2_listener_dirty = TRUE;
  } else {
    apply_i3dl2_listener_locked(props);
    i3dl2_listener_dirty = FALSE;
  }
  pthread_mutex_unlock(&stream_lock);
  return DS_OK;
}

HRESULT WINAPI IDirectSound_SetDistanceFactor(LPDIRECTSOUND sound, FLOAT factor,
                                              DWORD apply) {
  (void)sound;
  (void)apply;
  pthread_mutex_lock(&stream_lock);
  listener.distance_factor = factor > 0.0f ? factor : 1.0f;
  if (al_active && palSpeedOfSound)
    palSpeedOfSound(343.3f / listener.distance_factor);
  for (struct al_stream *s = streams; s; s = s->next)
    if (s->has_3d) s->dirty = TRUE;
  pthread_mutex_unlock(&stream_lock);
  return DS_OK;
}

HRESULT WINAPI IDirectSound_SetDopplerFactor(LPDIRECTSOUND sound,
                                             FLOAT factor, DWORD apply) {
  (void)sound; (void)apply;
  pthread_mutex_lock(&stream_lock);
  doppler_factor = clampf(factor, 0.0f, 10.0f);
  for (struct al_stream *s = streams; s; s = s->next)
    if (s->has_3d) s->dirty = TRUE;
  pthread_mutex_unlock(&stream_lock);
  return DS_OK;
}

HRESULT WINAPI IDirectSound_SetRolloffFactor(LPDIRECTSOUND sound, FLOAT factor,
                                             DWORD apply) {
  (void)sound;
  (void)apply;
  
  /* Lock the data. Change the rolloff factor. Mark the streams as dirty to do the update later. */
  pthread_mutex_lock(&stream_lock);
  listener.rolloff_factor = factor >= 0.0f ? factor : 1.0f;
  for (struct al_stream *stream = streams; stream; stream = stream->next) {
    stream->dirty = TRUE;
  }
  pthread_mutex_unlock(&stream_lock);
  return DS_OK;
}

HRESULT WINAPI IDirectSound_SetPosition(LPDIRECTSOUND sound, FLOAT x, FLOAT y,
                                        FLOAT z, DWORD apply) {
  (void)sound;
  (void)apply;
  
  /* Lock the data. Change the position. Mark the listener as dirty to do the update later. */
  pthread_mutex_lock(&stream_lock);
  listener.position[0] = x;
  listener.position[1] = y;
  listener.position[2] = z;
  listener.dirty_pos = TRUE;
  pthread_mutex_unlock(&stream_lock);
  return DS_OK;
}

HRESULT WINAPI IDirectSound_SetVelocity(LPDIRECTSOUND sound, FLOAT x, FLOAT y,
                                        FLOAT z, DWORD apply) {
  (void)sound;
  (void)apply;
  
  /* Lock the data. Change the velocity. Mark the listener as dirty to do the update later. */
  pthread_mutex_lock(&stream_lock);
  listener.velocity[0] = x;
  listener.velocity[1] = y;
  listener.velocity[2] = z;
  listener.dirty_vel = TRUE;
  pthread_mutex_unlock(&stream_lock);
  return DS_OK;
}

HRESULT WINAPI IDirectSound_SetOrientation(LPDIRECTSOUND sound, FLOAT x_front,
                                           FLOAT y_front, FLOAT z_front,
                                           FLOAT x_top, FLOAT y_top,
                                           FLOAT z_top, DWORD apply) {
  (void)sound;
  (void)apply;
  
  /* Lock the data. Change the orientation. Normalize the vectors. Mark the listener as dirty. */
  pthread_mutex_lock(&stream_lock);
  listener.front[0] = x_front;
  listener.front[1] = y_front;
  listener.front[2] = z_front;
  listener.top[0] = x_top;
  listener.top[1] = y_top;
  listener.top[2] = z_top;
  normalize3(listener.front);
  normalize3(listener.top);
  
  listener.dirty_ori = TRUE;
  pthread_mutex_unlock(&stream_lock);
  return DS_OK;
}

HRESULT WINAPI IDirectSound_CreateSoundStream(LPDIRECTSOUND sound,
                                              LPCDSSTREAMDESC description,
                                              LPDIRECTSOUNDSTREAM *result,
                                              LPUNKNOWN outer) {
  struct al_stream *stream = calloc(1, sizeof(*stream));
  const WAVEFORMATEX *format = description->lpwfxFormat;

  (void)sound;
  (void)outer;
  if (!stream)
    return E_OUTOFMEMORY;

  stream->object.lpVtbl = &stream_vtable;
  stream->reference_count = 1;
  stream->callback = description->lpfnCallback;
  stream->context = description->lpvContext;
  stream->adpcm = format && format->wFormatTag == WAVE_FORMAT_XBOX_ADPCM;
  stream->channels = format && format->nChannels == 2 ? 2 : 1;
  stream->sample_rate = format ? format->nSamplesPerSec : 0;
  stream->frequency = stream->sample_rate;
  stream->volume = 1.0f;
  stream->mix_left = 1.0f;
  stream->mix_right = 1.0f;
  stream->has_3d = (description->dwFlags & DSSTREAMCAPS_CTRL3D) != 0;
  stream->mode = DS3DMODE_NORMAL;
  stream->minimum_distance = DS3D_DEFAULTMINDISTANCE;
  stream->maximum_distance = DS3D_DEFAULTMAXDISTANCE;
  stream->i3dl2_gain = 1.0f;
  stream->doppler_pitch = 1.0f;
  stream->cone_inside = 360;
  stream->cone_outside = 360;
  stream->cone_outside_volume = 0; /* 0 mB = unity gain */
  stream->cone_orientation[0] = 0.0f;
  stream->cone_orientation[1] = 0.0f;
  stream->cone_orientation[2] = 1.0f;
  stream->filter_gain = 1.0f;
  stream->filter_gain_hf = 1.0f;
  stream->residual_bytes = 0;

  pthread_mutex_lock(&stream_lock);
  if (al_active) {
    palGenSources(1, &stream->source);
    if (has_efx && (stream->has_3d || stream->channels == 2) && global_reverb_slot) {
      palSource3i(stream->source, AL_AUXILIARY_SEND_FILTER, global_reverb_slot,
                  0, AL_FILTER_NULL);
    }
    update_source_properties(stream);
  }

  stream->next = streams;
  streams = stream;
  pthread_mutex_unlock(&stream_lock);

  *result = &stream->object;
  return DS_OK;
}

void __stdcall DirectSoundStopStream(LPDIRECTSOUNDSTREAM stream) {
  stream_flush(stream);
}

unsigned long __stdcall
DirectSoundGetStreamVoiceStatus(LPDIRECTSOUNDSTREAM stream) {
  struct al_stream *record = stream_from_interface(stream);
  pthread_mutex_lock(&stream_lock);
  unsigned long active = record->packet_count != 0;
  pthread_mutex_unlock(&stream_lock);
  return active;
}

#define STREAM_SETTER(body)                                                    \
  struct al_stream *record = stream_from_interface(stream);                    \
  /* Set the parameters. Mark the stream as dirty to do the update later. */   \
  pthread_mutex_lock(&stream_lock);                                            \
  body;                                                                        \
  record->dirty = TRUE;                                                        \
  pthread_mutex_unlock(&stream_lock);                                          \
  return DS_OK;

#define STREAM_SETTER_APPLY(body, apply)                                       \
  struct al_stream *record = stream_from_interface(stream);                    \
  /* Set the parameters. Mark the stream as dirty to do the update later. */   \
  pthread_mutex_lock(&stream_lock);                                            \
  body;                                                                        \
  record->dirty = TRUE;                                                        \
  pthread_mutex_unlock(&stream_lock);                                          \
  return DS_OK;

HRESULT WINAPI IDirectSoundStream_SetFrequency(LPDIRECTSOUNDSTREAM stream,
                                               DWORD frequency){
    STREAM_SETTER(record -> frequency = frequency ? frequency
                                                  : record->sample_rate)}

HRESULT WINAPI
    IDirectSoundStream_SetVolume(LPDIRECTSOUNDSTREAM stream, LONG volume){
        STREAM_SETTER(record->volume = gain_from_millibels(volume))}

HRESULT WINAPI IDirectSoundStream_SetMixBins(LPDIRECTSOUNDSTREAM stream,
                                             DWORD mix_bin_mask) {
  STREAM_SETTER(
      record->mix_left = (mix_bin_mask & DSMIXBIN_FRONT_LEFT) ? 1.0f : 0.0f;
      record->mix_right = (mix_bin_mask & DSMIXBIN_FRONT_RIGHT) ? 1.0f : 0.0f)
}

HRESULT WINAPI IDirectSoundStream_SetMixBinVolumes(LPDIRECTSOUNDSTREAM stream,
                                                   DWORD mix_bin_mask,
                                                   const LONG *volumes) {
  struct al_stream *record = stream_from_interface(stream);
  unsigned long bit, index = 0;

  pthread_mutex_lock(&stream_lock);
  /* Set the volumes. Mark the stream as dirty to do the update later. */
  for (bit = 0; bit < 32; bit++) {
    if (!(mix_bin_mask & (1UL << bit)))
      continue;
    if ((1UL << bit) == DSMIXBIN_FRONT_LEFT)
      record->mix_left = gain_from_millibels(volumes[index]);
    else if ((1UL << bit) == DSMIXBIN_FRONT_RIGHT)
      record->mix_right = gain_from_millibels(volumes[index]);
    index++;
  }
  record->dirty = TRUE;
  pthread_mutex_unlock(&stream_lock);
  return DS_OK;
}

HRESULT WINAPI IDirectSoundStream_SetMode(LPDIRECTSOUNDSTREAM stream,
                                          DWORD mode, DWORD apply){
    STREAM_SETTER_APPLY(record -> mode = mode, apply)}

HRESULT WINAPI
    IDirectSoundStream_SetPosition(LPDIRECTSOUNDSTREAM stream, FLOAT x, FLOAT y,
                                   FLOAT z, DWORD apply) {
  STREAM_SETTER_APPLY(record->position[0] = x; record->position[1] = y;
                      record->position[2] = z, apply)
}

HRESULT WINAPI IDirectSoundStream_SetVelocity(LPDIRECTSOUNDSTREAM stream,
                                              FLOAT x, FLOAT y, FLOAT z,
                                              DWORD apply) {
  STREAM_SETTER_APPLY(record->velocity[0] = x; record->velocity[1] = y;
                      record->velocity[2] = z, apply)
}

HRESULT WINAPI IDirectSoundStream_SetMinDistance(LPDIRECTSOUNDSTREAM stream,
                                                 FLOAT distance, DWORD apply){
    STREAM_SETTER_APPLY(record -> minimum_distance = distance, apply)}

HRESULT WINAPI IDirectSoundStream_SetMaxDistance(LPDIRECTSOUNDSTREAM stream,
                                                 FLOAT distance, DWORD apply){
    STREAM_SETTER_APPLY(record->maximum_distance = distance, apply)}

HRESULT WINAPI
    IDirectSoundStream_SetConeAngles(LPDIRECTSOUNDSTREAM stream, DWORD inside,
                                     DWORD outside, DWORD apply) {
  STREAM_SETTER_APPLY(record->cone_inside = inside;
                      record->cone_outside = outside, apply)
}

HRESULT WINAPI IDirectSoundStream_SetConeOrientation(LPDIRECTSOUNDSTREAM stream,
                                                     FLOAT x, FLOAT y, FLOAT z,
                                                     DWORD apply) {
  STREAM_SETTER_APPLY(record->cone_orientation[0] = x;
                      record->cone_orientation[1] = y;
                      record->cone_orientation[2] = z, apply)
}

HRESULT WINAPI IDirectSoundStream_SetConeOutsideVolume(
    LPDIRECTSOUNDSTREAM stream, LONG volume, DWORD apply){
    STREAM_SETTER_APPLY(record -> cone_outside_volume = volume, apply)}

HRESULT WINAPI
    IDirectSoundStream_SetI3DL2Source(LPDIRECTSOUNDSTREAM stream,
                                      LPCDSI3DL2BUFFER source, DWORD apply) {
  LONG direct, direct_hf;
  if (!source)
    return DS_OK;

  direct =
      source->lDirect +
      (LONG)(source->Obstruction.lHFLevel * source->Obstruction.flLFRatio) +
      (LONG)(source->Occlusion.lHFLevel * source->Occlusion.flLFRatio);
  if (direct > 0)
    direct = 0;

  direct_hf = source->Obstruction.lHFLevel + source->Occlusion.lHFLevel;
  if (direct_hf > 0)
    direct_hf = 0;

  STREAM_SETTER_APPLY(
      {
        record->i3dl2_gain = gain_from_millibels(direct);
        record->filter_gain = 1.0f; /* Do not double-attenuate overall volume,
                                       AL_GAIN handles this */
        if (direct_hf < direct)
          record->filter_gain_hf = gain_from_millibels(direct_hf - direct);
        else
          record->filter_gain_hf = 1.0f;
        record->filter_dirty = TRUE;
      },
      apply)
}

HRESULT WINAPI IDirectSoundStream_Pause(LPDIRECTSOUNDSTREAM stream,
                                        DWORD pause) {
  struct al_stream *record = stream_from_interface(stream);
  pthread_mutex_lock(&stream_lock);
  record->paused = (pause == DSSTREAMPAUSE_PAUSE);
  if (al_active && record->source) {
    if (record->paused)
      palSourcePause(record->source);
    else
      palSourcePlay(record->source);
  }
  pthread_mutex_unlock(&stream_lock);
  return DS_OK;
}

/* ---------- Dummy Buffer Implementation ---------- */

struct null_buffer {
  ULONG reference_count;
  LPVOID data;
  DWORD size;
  BOOL playing;
};

HRESULT WINAPI DirectSoundCreateBuffer(LPCDSBUFFERDESC description,
                                       LPDIRECTSOUNDBUFFER *result) {
  struct null_buffer *buffer = calloc(1, sizeof(*buffer));
  (void)description;
  if (!buffer)
    return E_OUTOFMEMORY;
  buffer->reference_count = 1;
  *result = (LPDIRECTSOUNDBUFFER)buffer;
  return DS_OK;
}

HRESULT WINAPI IDirectSound_CreateSoundBuffer(LPDIRECTSOUND sound,
                                              LPCDSBUFFERDESC description,
                                              LPDIRECTSOUNDBUFFER *result,
                                              LPUNKNOWN outer) {
  (void)sound;
  (void)outer;
  return DirectSoundCreateBuffer(description, result);
}

ULONG WINAPI IDirectSoundBuffer_Release(LPDIRECTSOUNDBUFFER buffer) {
  struct null_buffer *record = (struct null_buffer *)buffer;
  ULONG count = --record->reference_count;
  if (!count)
    free(record);
  return count;
}

HRESULT WINAPI IDirectSoundBuffer_SetBufferData(LPDIRECTSOUNDBUFFER buffer,
                                                LPVOID data, DWORD size) {
  struct null_buffer *record = (struct null_buffer *)buffer;
  record->data = data;
  record->size = size;
  return DS_OK;
}

HRESULT WINAPI IDirectSoundBuffer_Play(LPDIRECTSOUNDBUFFER buffer,
                                       DWORD reserved1, DWORD reserved2,
                                       DWORD flags) {
  (void)reserved1;
  (void)reserved2;
  (void)flags;
  ((struct null_buffer *)buffer)->playing = TRUE;
  return DS_OK;
}

HRESULT WINAPI IDirectSoundBuffer_Stop(LPDIRECTSOUNDBUFFER buffer) {
  ((struct null_buffer *)buffer)->playing = FALSE;
  return DS_OK;
}

HRESULT WINAPI IDirectSoundBuffer_SetCurrentPosition(LPDIRECTSOUNDBUFFER buffer,
                                                     DWORD play_cursor) {
  (void)buffer;
  (void)play_cursor;
  return DS_OK;
}
HRESULT WINAPI IDirectSoundBuffer_SetLoopRegion(LPDIRECTSOUNDBUFFER buffer,
                                                DWORD loop_start,
                                                DWORD loop_length) {
  (void)buffer;
  (void)loop_start;
  (void)loop_length;
  return DS_OK;
}
HRESULT WINAPI IDirectSoundBuffer_SetPitch(LPDIRECTSOUNDBUFFER buffer,
                                           LONG pitch) {
  (void)buffer;
  (void)pitch;
  return DS_OK;
}
HRESULT WINAPI IDirectSoundBuffer_SetVolume(LPDIRECTSOUNDBUFFER buffer,
                                            LONG volume) {
  (void)buffer;
  (void)volume;
  return DS_OK;
}

void dsound_openal_stream_set_stereo_position(IDirectSoundStream *object, BOOL positioned, float pan,
                                           float distance, float minimum_distance, float distance_fade) {
  struct al_stream *stream = (struct al_stream *)object;
  (void)distance;
  (void)minimum_distance;

  pthread_mutex_lock(&stream_lock);
  if (positioned && stream->channels == 2) {
    stream->stereo_positioned = TRUE;
    stream->stereo_pan = pan < -1.0f ? -1.0f : (pan > 1.0f ? 1.0f : pan);
    stream->stereo_distance_fade = distance_fade < 0.0f ? 0.0f : (distance_fade > 1.0f ? 1.0f : distance_fade);
  } else {
    stream->stereo_positioned = FALSE;
    stream->stereo_pan = 0.0f;
    stream->stereo_distance_fade = 1.0f;
  }
  update_source_properties(stream);
  pthread_mutex_unlock(&stream_lock);
}
