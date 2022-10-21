#ifndef MY_DEFINES_HPP
#define MY_DEFINES_HPP

#include <cstdint>
#include <vector>
#include <string>

#include <cassert>

#define ctu64(x) static_cast<uint64_t>(x)
#define cti64(x) static_cast<int64_t>(x)

#define ctu32(x) static_cast<uint32_t>(x)
#define cti32(x) static_cast<int32_t>(x)

#define ctu16(x) static_cast<uint16_t>(x)
#define cti16(x) static_cast<int16_t>(x)

#define ctu8(x) static_cast<uint8_t>(x)
#define cti8(x) static_cast<int8_t>(x)

static const uint64_t NegativeUInt64 = -1;
static const uint32_t NegativeUInt32 = -1;
static const uint16_t NegativeUInt16 = -1;
static const uint8_t NegativeUInt8 = -1;

static const int32_t Int32Max = INT32_MAX;

// Comment these out if someone else declared these already.
typedef uint64_t u64;
typedef uint32_t u32;
typedef uint16_t u16;
typedef uint8_t u8;

typedef int64_t i64;
typedef int32_t i32;
typedef int16_t i16;
typedef int8_t i8;
//


// ============================================================================
// reminder it can be further helpful to place a breakpoint on the asserts statements.

// if condition is false, it throws exception.
void qassert(const bool bCondition, const std::string& strText);

// forced qassert. unconditional exception throw.
void fqassert(const std::string& strText);



#endif
