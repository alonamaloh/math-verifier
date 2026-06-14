#ifndef MATH_TIMING_HPP
#define MATH_TIMING_HPP

#include <ctime>

// Monotonic clock reading in nanoseconds, for coarse task timing
// (MATH_TIME_TACTICS, MATH_TIME_DECLARATIONS, MATH_REPORT_ADDDECL,
// MATH_CLAIM_SIZES, kernel add-declaration accounting, ...).
//
// We deliberately avoid <chrono> here. clang built against libstdc++ 13's
// <chrono> hits a consteval bug — `hh_mm_ss::_S_fractional_width()` is
// invoked in a non-constant context — that aborts the build, so the
// project could not be compiled with clang on a stock Linux toolchain.
// clock_gettime(CLOCK_MONOTONIC) is POSIX, header-light, and behaves
// identically under clang and g++ on both Linux and macOS, so it keeps the
// timing instrumentation portable across every toolchain we build with.
inline long long monotonicNanos() {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return static_cast<long long>(ts.tv_sec) * 1000000000LL
         + static_cast<long long>(ts.tv_nsec);
}

#endif  // MATH_TIMING_HPP
