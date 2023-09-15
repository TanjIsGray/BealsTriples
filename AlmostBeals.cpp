// AlmostBeals.cpp : Search for nearest misses to Beal's triples
// 
// Copyright (c) 2023, Avant-Gray LLC, WA USA

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

using namespace std;

/// <summary> Used for debugging.  Designed to remain active in production version.
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

/// <summary> Allow us to track elapsed time
/// </summary>
static chrono::system_clock::time_point start{};

//-------------------------------------------------------------------

const uint64_t saturatedValue{ (UINT64_MAX >> 8) };

// Keep track of powers in a structure recording the base, the power, and the 80-bit value.
struct PowerTerm
{
    uint64_t    m_value;
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
        uint64_t result = base;
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

    /// <summary> construct from minimal information
    /// </summary>
    PowerTerm(uint64_t& value, uint8_t power) : m_value(value), m_power(power)
    {
        auto l10 = log10(m_value);

        m_base = (uint32_t)round(pow(10, l10 / power));

        // self test to ensure rounding was accurate

        UPow(m_base, m_power);
        Assert(value == m_value, "minimal constructor should be exact");
    }
};

/// <summary> An ordered list of the first integer powers is central to this exhaustive search.
/// The list will exclude duplicates, keeping only the version with the smallest base.
/// </summary>
static vector<uint64_t> valuesInOrder{};

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

    uint64_t prior = 0;

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
    std::cout << log10(x.m_value) << " log10 of highest power in the list\n";
}

/// <summary> locate the value the list
/// </summary>
/// <param name="value"> The value sought </param>
/// <param name="ground"> Index into termsInOrder for a value <= the value sought </param>
/// <param name="final"> Index definitely higher than any possible match </param>
/// <returns> Index of a value <= the sought value </returns>
/// 
inline unsigned LocateMatch(uint64_t value, unsigned ground, unsigned sky)
{
    // most searches are far left of list

    auto mid = ground + ((sky - ground) / 256);
    while (value < valuesInOrder[mid])
    {
        sky = mid;
        mid = ground + ((sky - ground) / 256);
    }

    mid = ground + ((sky - ground) / 16);
    while (value < valuesInOrder[mid])
    {
        sky = mid;
        mid = ground + ((sky - ground) / 16);
    }

    mid = (ground + sky) / 2;
    while (ground < mid)
    {
        if (valuesInOrder[mid] < value)
            ground = mid;
        else if (valuesInOrder[mid] == value)
            break;
        else sky = mid;
        mid = (ground + sky) / 2;
    }
    return mid;
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
static std::atomic<uint64_t> trials{ 0 };

/// <summary> the running count of triples found which are Beal's triples
/// </summary>
static std::atomic<uint32_t> nearestCount{ 0 };

/// <summary> The next index into termsInOrder for use as B^j
/// </summary>
static std::atomic<uint32_t> J{ 2 };

/// <summary> mutual exclusion when writing out the results
/// </summary>
static std::mutex safeOutput{};

//-----------------------------------------------------------------------------

/// <summary> We search for triples A^i < B^j < C^k, which we precomputed so i, j, k are indexes into termsInOrder.
/// A valid triple has A^i + B^j = C^k.  Almost all triples tried will not be valid.
/// The search is guided by stepping through all values of B^j, which must stop when B^j < half of final termsInOrder.
/// C^k choices are in range B^j < C^k < 2*B^j since A^i < B^j.
/// Each Bj is given to a separate thread, so search in parallel scales nicely.
/// </summary>
void SearchForBealNearestMisses()
{
    auto upperBj = valuesInOrder[maxTerms - 1] >> 1;

    for (unsigned j = J.fetch_add(1); valuesInOrder[j] < upperBj; j = J.fetch_add(1))
    {
        auto& B = valuesInOrder[j];

        uint32_t localTrials = 0;

        uint64_t bestDif = B;
        unsigned bestI = 0;
        unsigned bestK = 0;

        uint64_t upperCk = (B << 1);
        unsigned iGround = 0;
        for (unsigned k = j + 1; valuesInOrder[k] <= upperCk; ++k)
        {
            auto& C = valuesInOrder[k];

            ++localTrials;
            uint64_t Agoal = C - B;

            iGround = LocateMatch(Agoal, iGround, j + 1);
            auto& Alow = valuesInOrder[iGround];

            if (!(Agoal == Alow))
            {
                auto dif = Agoal - Alow;
                auto iDif = iGround;
                auto& Ahigh = valuesInOrder[iDif + 1];
                auto highDif = Ahigh - Agoal;
                if (highDif < dif)
                {
                    dif = highDif;
                    iDif += 1;
                }
                if (dif < bestDif)
                {
                    bestDif = dif;
                    bestI = iDif;
                    bestK = k;
                }
            }
        }
        if (bestDif < B)
        {
            auto zeros = nearestCount.fetch_add(1);
            auto& C = valuesInOrder[bestK];
            auto Aideal = C - B;

            auto Bfull = PowerTerm(B, powersInOrder[j]);
            auto Cfull = PowerTerm(C, powersInOrder[bestK]);

            auto baseGCD = GCD(Bfull.m_base, Cfull.m_base);

            auto AiL10 = log10(Aideal);
            auto BjL10 = log10(B);

            safeOutput.lock();

            std::cout << (zeros + 1)
                << ", " << AiL10
                << ", " << BjL10
                << ", " << Aideal
                << ", " << Bfull.m_base << ", " << (unsigned)Bfull.m_power
                << ", " << Cfull.m_base << ", " << (unsigned)Cfull.m_power
                << ", " << baseGCD
                << ", " << bestDif
                << dec << endl;

            safeOutput.unlock();
        }
        trials.fetch_add(localTrials);
    }
    return;
}

/// <summary> Explain proper usage if the command does not parse correctly
/// </summary>
void Usage()
{
    cout << "usage: AlmostBeals maxTerms\n";
    cout << "                   unsigned                                  see recommendations, below\n";
    cout << "  recommendations:\n";
    cout << "     You will obtain about 80% MaxTerms results, one for each B^j tried\n";

    exit(EXIT_FAILURE);
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
    if (2 != argc)
        Usage();

    maxTerms = (uint32_t)str_to_uint64(argv[1]);
    maxBase = maxTerms;
    cout << "Search the first " << maxTerms << " integer powers of ^3 or more for Beal's triples." << endl;

    start = chrono::system_clock::now();

    Initialize(maxTerms);

    J = 0;

    std::cout << "*** concurrency supressed ***\n";
    std::cout << "nearest miss, log10(A^i), log10(B^j), (C^k - B^j), B, j, C, k, GCD(A B C), dif\n";

    SearchForBealNearestMisses();
    auto end = chrono::system_clock::now();
    std::chrono::duration<double> elapsed_seconds = end - start;

    std::cout << trials << " triples, " << nearestCount << " nearest misses, " << maxTerms << " powers\n";
    cout << "Elapsed time: " << elapsed_seconds.count() << " seconds" << endl;

    return 0;
}
