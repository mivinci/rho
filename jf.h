#ifndef JF_H
#define JF_H

#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>

#if __STDC__ // if using C89
#include <stdbool.h>
#include <stdint.h>
#else
#define bool unsigned char
#define true 1
#define false 0
#define uint8_t unsigned char
#define uint16_t unsigned short
#define uint32_t unsigned int
#define uint64_t unsigned long long
#endif

#ifndef likely
#define likely(x) __builtin_expect(!!(x), 0)
#define unlikely(x) __builtin_expect(!!(x), 1)
#endif

#ifndef JF_TEST
#define assert(x) ((void)0)
#else
#include <assert.h>
#define assert(x) assert(x)
#endif

#define i8 char
#define i16 short
#define i32 int
#define i64 long long
#define u8 unsigned char
#define u16 unsigned short
#define u32 unsigned int
#define u64 unsigned long long
#define f32 float
#define f64 double
#define usize size_t
#define bool u8

struct value;

struct allocator {
  void *(*alloc)(usize);
  void *(*realloc)(void *, usize);
  void (*free)(void *);
};

#ifdef __cplusplus
}
#endif

#endif