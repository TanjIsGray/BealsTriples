// Beal64.cpp : Search for Beal's triples within a total compatible with 128-bit unsigned
// 
// Copyright (c) 2023, Avant-Gray LLC, WA USA
// Released Sept 2023 as-is, with no warranty of fitness for any purpose,
//      by Avant-Gray LLC to GitHub under Apache v.2 license

// C++ standard libraries

#include <stdlib.h>
#include <math.h>
#include <random>
#include <cstdint>
#include <array>
#include <vector>
#include <queue>
#include <algorithm>
#include <bit>
#include <bitset>
#include <unordered_map>
#include <iostream>
#include <sstream>
#include <thread>
#include <atomic>
#include <mutex>
#include <chrono>
#include <ctime>

#if defined(_MSC_VER)
// Visual Studio version of 128-bit support (minimal, see custom type below)
#include <intrin.h>
#pragma intrinsic(_umul128)
#else
//  GCC version of 128-bit support
    typedef unsigned int uint128_t __attribute__((mode(TI)));
#endif

using namespace std;

/// <summary> Used for debugging.  Designed to remain active in release version.
/// </summary>
void Assert(bool constraint, const char* reason)
{
    if (!constraint)
    {
        std::cout << "Assert failed: " << reason << endl;
        std::exit(EXIT_FAILURE);
    }
}

//-------------------------------------------------------------------
// This command-line parameter guides the scale of the search.

/// <summary> The size of the list of terms by least value of (base ^ power).
/// </summary>
static unsigned maxTerms = 0;

/// <summary> (maxBase - 1) is the largest base integer used to create any power.
/// Using maxTerms guarantees that all least powers will be included.
/// In practice the last few percent of bases are never used.
/// </summary>
static unsigned maxBase = 0;

/// <summary> Using an 80-bit unsigned so we will track powers up to 79
/// </summary>
static const unsigned maxPower = 80;

static uint64_t resumeHi = 0, resumeLo = 0;

/// <summary> Allow us to track elapsed time
/// </summary>
static chrono::system_clock::time_point start {};

//-------------------------------------------------------------------

#if defined(_MSC_VER)

static const double two64 = pow(2.0, 64);

/// <summary> This is not a complete implementation of uint128_t.  Just enough for our needs here.
/// </summary>
struct uint128_t
{
    uint64_t    m_lo;
    uint64_t    m_hi;

    /// <summary> Default constructor
    /// </summary>
    uint128_t()
    {
        m_lo = 0;
        m_hi = 0;
    }

    /// <summary> Construct from a 64-bit (or smaller) unsigned int
    /// </summary>
    uint128_t(uint64_t lo) : m_lo(lo), m_hi(0)
    {}

    /// <summary> Construct all 128-bits from two 64-bit unsigned ints
    /// </summary>
    uint128_t(uint64_t lo, uint64_t hi) : m_lo(lo), m_hi(hi)
    {}

    /// <summary> Copy-constructor
    /// </summary>
    uint128_t(const uint128_t& a) : m_lo(a.m_lo), m_hi(a.m_hi)
    {}

    /// <summary> Assignment operator
    /// </summary>
    void operator=(const uint128_t& a)
    {
        m_lo = a.m_lo;
        m_hi = a.m_hi;
    }

    /// <summary> Equality operator: this == a
    /// </summary>
    bool operator==(const uint128_t& a) const
    {
        return (m_hi == a.m_hi) && (m_lo == a.m_lo);
    }

    /// <summary> less-than operator: this < a
    /// </summary>
    bool operator<(const uint128_t& a) const
    {
        return (m_hi < a.m_hi)
            || ((m_hi == a.m_hi) && (m_lo < a.m_lo));
    }

    /// <summary> Less-than-or-equal operator: this <= a
    /// </summary>
    bool operator<=(const uint128_t& a) const
    {
        return (m_hi < a.m_hi)
            || ((m_hi == a.m_hi) && (m_lo <= a.m_lo));
    }

    /// <summary> Addition operator: this + a
    /// </summary>
    uint128_t operator+(const uint64_t& a) const
    {
        uint128_t result;
        result.m_lo = m_lo + a;
        result.m_hi += (result.m_lo < m_lo) ? 1 : 0;
        return result;
    }

    /// <summary> subtraction operator: this - a
    /// </summary>
    uint128_t operator-(const uint128_t& a) const
    {
        uint128_t result;
        result.m_lo = m_lo - a.m_lo;
        result.m_hi -= a.m_hi + (m_lo < result.m_lo) ? 1 : 0;
        return result;
    }

    /// <summary> shift-right operator: this >> a
    /// </summary>
    uint128_t operator>>(unsigned a) const
    {
        uint128_t result{ m_lo, m_hi };
        while (64 <= a)
        {
            result.m_lo = result.m_hi;
            result.m_hi = 0;
            a -= 64;
        }
        result.m_lo = (result.m_hi << (64 - a)) | (result.m_lo >> a);
        result.m_hi = result.m_hi >> a;
        return result;
    }

    /// <summary> shift-left operator: this << a
    /// </summary>
    uint128_t operator<<(unsigned a) const
    {
        uint128_t result{ m_lo, m_hi };
        while (64 <= a)
        {
            result.m_hi = m_lo;
            result.m_lo = 0;
            a -= 64;
        }
        result.m_hi = (m_lo >> (64 - a)) | (m_hi << a);
        result.m_lo = result.m_lo << a;
        return result;
    }

    /// <summary> multiply opearator, up to 64-bits: this * a
    /// </summary>
    uint128_t operator*(const uint64_t& a) const
    {
        uint64_t temp;
        uint128_t result{ _umul128(m_lo, a, &temp), m_hi * a };
        result.m_hi += temp;

        return result;
    }

    /// <summary> double precision is good enough
    ///    to identify any root >= cube of a number up to saturatedValue
    /// </summary>
    double Log10()
    {
        auto temp = (two64 * (double)m_hi) + m_lo;

        return log10(temp);
    }
};


// the saturated value is used to stop arithmetic safely some distance below overflow

const uint128_t saturatedValue{ (UINT64_MAX << 56), (UINT64_MAX >> 8) };
#else
const uint128_t saturatedValue = ((uint128_t) UINT64_MAX) << 56;
#endif

/// <summary> Keep track of powers in a structure recording the base, the power, and the 80-bit value.
/// </summary>
struct PowerTerm
{
    uint128_t   m_value;
    uint32_t    m_base;
    uint8_t     m_power;

    /// <summary> initialize to zeroes
    /// </summary>
    PowerTerm()
        : m_value(0)
        , m_base(0)
        , m_power(0)
    {}

    /// <summary> compare backwards to put the least at top of priority queue
    /// </summary>
    bool operator<(const PowerTerm& a) const
    {
        return (a.m_value < m_value)
            || ((a.m_value == m_value) && (a.m_base < m_base));
    }

    /// <summary>  calculate an 80- bit unsigned power, truncated
    /// </summary>
    void UPow(uint64_t base, unsigned power)
    {
        //  GCC version of 128-bit support
        uint128_t result = base;
        if ((power * log10(base)) < 37)
        {
            while ((0 < --power))
            {
                result = result * base;
            }
            m_value = (saturatedValue <= result) ? saturatedValue : result;
        }
        else
            m_value = saturatedValue;
    }

#if defined(_MSC_VER)
    double Log10()
    {
        auto temp = (double)m_value.m_hi;
        temp *= (1ull << 32);
        temp *= (1ull << 32);
        temp += m_value.m_lo;

        return log10(temp);
    }
#else
    double Log10()
    {
        double temp = m_value;
        return log10(temp);
    }
#endif

    /// <summary> construct from minimal information
    /// </summary>
    PowerTerm(uint128_t& value, uint8_t power) : m_value(value), m_power(power)
    {
        auto l10 = Log10();

        m_base = (uint32_t)round(pow(10, l10 / power));

        // self test to ensure rounding was accurate

        UPow(m_base, m_power);
        Assert(value == m_value, "minimal constructor should be exact");
    }
};

/// <summary> An ordered list of the first integer powers is central to this exhaustive search.
/// The list will exclude duplicates, keeping only the version with the smallest base.
/// </summary>
static vector<uint128_t> valuesInOrder {};

/// <summary> The base can be reconstructed from the value and the power, minimizing memory use for the vectors.
/// </summary>
static vector<uint8_t> powersInOrder{};

/// <summary> fill the list of integer powers in rising order without duplicates.
/// </summary>
void Initialize(unsigned numberOfTerms)
{
    // avoid needing to grow these potentially huge vectors by preallocating their capacity.

    valuesInOrder.reserve(maxTerms);
    powersInOrder.reserve(maxTerms);

    // the power term is used for values in active use, but not used for bulk storage

    PowerTerm x = {};
    std::priority_queue<PowerTerm> shunt = {};

    // all powers of 1 are represented by a special entry

    x.m_base = 1;
    x.m_power = 3;
    x.m_value = 1;
    valuesInOrder.push_back(x.m_value);
    powersInOrder.push_back(x.m_power);

    // The priority queue is initialized with all owers of 2 that fit within our arithmetic.

    for (unsigned power = 3; power < maxPower; ++power)
    {
        x.m_base = 2;
        x.m_power = power;
        x.UPow(2, power);
        shunt.push(x);
    }

    // we then pull numbers out in rising order, replacing each value with a raised base
    // of the same power, and fill the ordered list of integer powers, skipping duplicates

    // the PwerTerm ordering function sorts for minimum base, when value is duplicate.

    uint128_t prior = 0;

    while (valuesInOrder.size() < maxTerms)
    {
        x = shunt.top();
        shunt.pop();
        Assert(prior <= x.m_value, "priority queue must deliver in order");
        Assert(x.m_value < saturatedValue, "the termsInOrder should not include any overflows");
        if (prior < x.m_value)
        {
            valuesInOrder.push_back(x.m_value);
            powersInOrder.push_back(x.m_power);
            prior = x.m_value;
        }
        x.m_base++;
        x.UPow(x.m_base, x.m_power);
        shunt.push(x);
    }

    x.m_base = 0;  // not used for Log10
    x.m_power = powersInOrder[maxTerms - 1];
    x.m_value = valuesInOrder[maxTerms - 1];
    std::cout << (x.Log10()) << " log10 of highest power in the list\n";
}

/// <summary> locate the value the list
/// </summary>
/// <returns> Index of the greatest value <= the sought value </returns>
/// 
inline unsigned LocateFromLeft(uint128_t value, unsigned ground, unsigned step, unsigned sky)
{
    // most searches are solved near left edge of list

    auto mid = ground + step;
    while ((mid < sky) && (valuesInOrder[mid] <= value))
    {
        ground = mid;
        mid += step;
    }

    mid = ground + 1;
    while ((mid < sky) && (valuesInOrder[mid] <= value))
    {
            ground = mid;
            mid += 1;
    }
    return ground;
}

/// <summary> find the greatest common divisor of two unsigned integers (base values).
/// </summary>
unsigned GCD(unsigned p, unsigned q)
{
    if (q < p)
    {
        auto temp = p;
        p = q;
        q = temp;
    }

    while (0 < p)
    {
        auto r = q % p;
        q = p;
        p = r;
    }
    return q;
}

//-----------------------------------------------------------------------------

// These variables are shared by all the threads.
// They ideally would be in separate cache lines to avoid false sharing,
//      but they are not used intensely enough to be worth forcing their layout.

/// <summary> the running count of all triples constructed and tested
/// </summary>
static std::atomic<uint64_t> trials {0};

/// <summary> the running count of triples found which are Beal's triples
/// </summary>
static std::atomic<uint32_t> zerosCount {0};

/// <summary> The next index into termsInOrder for use as B^j
/// </summary>
static std::atomic<uint32_t> J {2};

/// <summary> mutual exclusion when writing out the results
/// </summary>
static std::mutex safeOutput {};

//-----------------------------------------------------------------------------

/// <summary> We search for triples A^i < B^j < C^k, which we precomputed so i, j, k are indexes into termsInOrder.
/// A valid triple has A^i + B^j = C^k.  Almost all triples tried will not be valid.
/// The search is guided by stepping through all values of B^j, which must stop when B^j < half of final termsInOrder.
/// C^k choices are in range B^j < C^k < 2*B^j since A^i < B^j.
/// Each Bj is given to a separate thread, so search in parallel scales nicely.
/// </summary>
void SearchForBeal()
{
    auto upperBj = valuesInOrder[maxTerms - 1] >> 1;

    for (unsigned j = J.fetch_add(1); valuesInOrder[j] < upperBj; j = J.fetch_add(1))
    {
        auto& B = valuesInOrder[j];

        uint32_t localTrials = 0;

        uint128_t upperCk = (B << 1);
        unsigned iGround = 0;
        unsigned step = 32;
        for (unsigned k = j + 1; valuesInOrder[k] <= upperCk; ++k)
        {
            auto& C = valuesInOrder[k];

            ++localTrials;
            uint128_t delta = C - B;

            auto iPrev = iGround;
            iGround = LocateFromLeft(delta, iGround, step, j + 1);
            step = (iGround - iPrev + 2) / 2;
            auto& A = valuesInOrder[iGround];

            if (delta == A)
            {
                auto tries = trials.fetch_add(localTrials);
                auto zeros = zerosCount.fetch_add(1);
                localTrials = 0;

                auto Afull = PowerTerm(A, powersInOrder[iGround]);
                auto Bfull = PowerTerm(B, powersInOrder[j]);
                auto Cfull = PowerTerm(C, powersInOrder[k]);

                auto baseGCD = GCD(GCD(Afull.m_base, Bfull.m_base), Cfull.m_base);

                auto AiL10 = Afull.Log10();
                auto BjL10 = Bfull.Log10();

                safeOutput.lock();

                std::cout << tries << ", " << (zeros + 1)
                    << ", " << AiL10
                    << ", " << BjL10
                    << ", " << Afull.m_base << ", " << (unsigned)Afull.m_power
                    << ", " << Bfull.m_base << ", " << (unsigned)Bfull.m_power
                    << ", " << Cfull.m_base << ", " << (unsigned)Cfull.m_power
                    << ", " << baseGCD
                    << dec << endl;

                if ((1900 < zeros) && (0 == (zeros % 100)))
                {
                    auto end = chrono::system_clock::now();
                    std::chrono::duration<double> elapsed_seconds = end - start;
                    std::cout << "Elapsed time: " << elapsed_seconds.count() << " seconds" << endl;
                    std::cout << std::flush;
                }

                // pause slightly to avoid cout collisions
                // std::this_thread::sleep_for(std::chrono::milliseconds(100));
                safeOutput.unlock();
            }
        }
        trials.fetch_add(localTrials);
    }
    return;
}

/// <summary> Explain proper usage if the command does not parse correctly
/// </summary>
void Usage()
{
    std::cout << "usage: Beal64 maxTerms log10(Bj)resume\n";
    std::cout << "              unsigned                                  see recommendations, below\n";
    std::cout << "                       0 begin at start                 or use output value from a prior run\n";
    std::cout << "  recommendations:\n";
    std::cout << "     1e6 terms will find 1519 triples in a couple of minutes on  on an 8-core Icelake\n";
    std::cout << "     1e7 terms will deliver the first 4.8 thousand Beal triples in a few hours\n";
    std::cout << "     1e8 terms will run for about 10 days on an 8 core IceLake at 2.3 GHz\n";
    std::cout << "     regardless of the resume value, the last Bj term tried will stay the same\n";

    exit(EXIT_FAILURE);
}

/// <summary> use power to approximate a big number
/// </summary>
uint128_t str_to_uint128(const char* str)
{
    stringstream ss(str);
    double log10input;
    ss >> log10input;
    auto tens = (unsigned)floor(log10input);
    auto mantissa = (unsigned)floor(1024 * pow(10.0, log10input - tens));

    Assert(tens < 36, "big numbers limited to < 10^37");

    uint128_t result = 1;

    while (0 < tens)
    {
        result = result * 10;
    }
    result = result * mantissa;
    return result >> 10;
}

/// <summary> use double to enable exponential notation like "1e6"
/// </summary>
uint64_t str_to_uint64(const char* str)
{
    stringstream ss(str);
    double num;
    ss >> num;
    return (uint64_t)round(num);
}

/// <summary> use double to enable exponential notation like "1e6"
/// </summary>
bool str_to_bool(const char* str)
{
    stringstream ss(str);
    bool truth = false;
    if ((NULL != str) && (0 != str[0]))
    {
        if (('T' == str[0]) || ('t' == str[0]))
            truth = true;
    }
    return truth;
}

/// <summary> initialize, launch parallel search threads, await all threads then finish
/// </summary>
int main(
    int argc,       // Number of strings in array argv
    char* argv[],   // Array of command-line argument strings
    char* envp[]    // Array of environment variable strings
)
{
    if (3 != argc)
        Usage();

    maxTerms = (uint32_t) str_to_uint64(argv[1]);
    maxBase = maxTerms;
    std::cout << "Search the first " << maxTerms << " integer powers of ^3 or more for Beal's triples." << endl;

    auto resume = str_to_uint128(argv[2]);
    std::cout << hex << "Search begins for B^j = " << resumeHi << ':' << resumeLo << dec << ", log10(Bj) = " << argv[2] << endl;

    start = chrono::system_clock::now();

    Initialize(maxTerms);

    unsigned firstJ = 0;
    uint64_t threshold = (resumeHi << 48) | (resumeLo >> 16);

    while (valuesInOrder[firstJ] < threshold)
        ++firstJ;

    J = firstJ;

//#define NO_THREADS 1
#ifdef NO_THREADS	// recommend no threads if you need to debug code
    std::cout << "*** concurrency supressed ***\n";
    std::cout << "trials, zeros, log10(A^i), log10(B^j), A, i, B, j, C, k, GCD(A B C)\n";

    SearchForBeal();
#else
// hardware concurrency is normally implemented as the number of virtual cores directly implemented by the CPU.

    unsigned concurrency = std::thread::hardware_concurrency();
    std::cout << "hardware concurrency: " << concurrency << endl;

    std::cout << "trials, zeros, log10(A^i), log10(B^j), A, i, B, j, C, k, GCD(A B C)\n";

    vector<thread*> threads = {};

    for (unsigned t = 0; t < concurrency; ++t)
    {
        threads.push_back(new std::thread(SearchForBeal));
    }

    // wait for the threads to finish

    for (auto th : threads)
        th->join();

#endif
    auto end = chrono::system_clock::now();
    std::chrono::duration<double> elapsed_seconds = end - start;

    std::cout << trials << " triples, " << zerosCount << " zeros, " << maxTerms << " powers\n";
    std::cout << "Elapsed time: " << elapsed_seconds.count() << " seconds" << endl;

    return 0;
}
