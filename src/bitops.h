#ifdef GPSFISH

/// lsb()/msb() finds the least/most significant bit in a nonzero uint64_t.
/// pop_lsb() finds and clears the least significant bit in a nonzero uint64_t.

#if defined(USE_BSFQ)

#  if ( defined(_MSC_VER) || defined(_WIN32) ) && !defined(__INTEL_COMPILER)

FORCE_INLINE uint32_t lsb(uint64_t b) {
  unsigned long index;
  _BitScanForward64(&index, b);
  return (uint32_t) index;
}

FORCE_INLINE uint32_t msb(uint64_t b) {
  unsigned long index;
  _BitScanReverse64(&index, b);
  return (uint32_t) index;
}

#  else

FORCE_INLINE uint32_t lsb(uint64_t b) { // Assembly code by Heinz van Saanen
  uint64_t index;
  __asm__("bsfq %1, %0": "=r"(index): "rm"(b) );
  return (uint32_t) index;
}

FORCE_INLINE uint32_t msb(uint64_t b) {
  uint64_t index;
  __asm__("bsrq %1, %0": "=r"(index): "rm"(b) );
  return (uint32_t) index;
}

#  endif

FORCE_INLINE uint32_t pop_lsb(uint64_t* b) {
  const uint32_t s = lsb(*b);
  *b &= ~(1ULL << s);
  return s;
}

#else // if !defined(USE_BSFQ)

extern uint32_t msb(uint64_t b);
extern uint32_t lsb(uint64_t b);
extern uint32_t pop_lsb(uint64_t* b);

#endif

#endif
