#include <iostream>
#include <vector>
#include <string>
#include <complex>
#include <cstring>
#include <cassert>
#include <cstdint>
#include <cstddef>

#include <chrono>

namespace hint
{
    using Float32 = float;
    using Float64 = double;
    using Complex32 = std::complex<Float32>;
    using Complex64 = std::complex<Float64>;

    constexpr Float64 HINT_PI = 3.141592653589793238462643;
    constexpr Float64 HINT_2PI = HINT_PI * 2;
    constexpr Float64 COS_PI_8 = 0.707106781186547524400844;

    constexpr size_t FFT_MAX_LEN = size_t(1) << 23;

    template <typename T>
    constexpr T int_floor2(T n)
    {
        constexpr int bits = sizeof(n) * 8;
        for (int i = 1; i < bits; i *= 2)
        {
            n |= (n >> i);
        }
        return (n >> 1) + 1;
    }

    template <typename T>
    constexpr T int_ceil2(T n)
    {
        constexpr int bits = sizeof(n) * 8;
        n--;
        for (int i = 1; i < bits; i *= 2)
        {
            n |= (n >> i);
        }
        return n + 1;
    }

    template <typename IntTy>
    constexpr bool is_2pow(IntTy n)
    {
        return n != 0 && (n & (n - 1)) == 0;
    }

    // 求整数的对数
    template <typename T>
    constexpr int hint_log2(T n)
    {
        constexpr int bits = sizeof(n) * 8;
        int l = -1, r = bits;
        while ((l + 1) != r)
        {
            int mid = (l + r) / 2;
            if ((T(1) << mid) > n)
            {
                r = mid;
            }
            else
            {
                l = mid;
            }
        }
        return l;
    }
    constexpr int hint_ctz(uint32_t x)
    {
        int r0 = 31;
        x &= (-x);
        if (x & 0x55555555)
        {
            r0 &= ~1;
        }
        if (x & 0x33333333)
        {
            r0 &= ~2;
        }
        if (x & 0x0F0F0F0F)
        {
            r0 &= ~4;
        }
        if (x & 0x00FF00FF)
        {
            r0 &= ~8;
        }
        if (x & 0x0000FFFF)
        {
            r0 &= ~16;
        }
        r0 += (x == 0);
        return r0;
    }

    constexpr int hint_ctz(uint64_t x)
    {
        int r0 = 63;
        x &= (-x);
        if (x & 0x5555555555555555)
        {
            r0 &= ~1; // -1
        }
        if (x & 0x3333333333333333)
        {
            r0 &= ~2; // -2
        }
        if (x & 0x0F0F0F0F0F0F0F0F)
        {
            r0 &= ~4; // -4
        }
        if (x & 0x00FF00FF00FF00FF)
        {
            r0 &= ~8; // -8
        }
        if (x & 0x0000FFFF0000FFFF)
        {
            r0 &= ~16; // -16
        }
        if (x & 0x00000000FFFFFFFF)
        {
            r0 &= ~32; // -32
        }
        r0 += (x == 0);
        return r0;
    }

    // Leading zeros
    constexpr int hint_clz(uint32_t x)
    {
        constexpr uint32_t MASK32 = uint32_t(0xFFFF) << 16;
        int res = sizeof(uint32_t) * CHAR_BIT;
        if (x & MASK32)
        {
            res -= 16;
            x >>= 16;
        }
        if (x & (MASK32 >> 8))
        {
            res -= 8;
            x >>= 8;
        }
        if (x & (MASK32 >> 12))
        {
            res -= 4;
            x >>= 4;
        }
        if (x & (MASK32 >> 14))
        {
            res -= 2;
            x >>= 2;
        }
        if (x & (MASK32 >> 15))
        {
            res -= 1;
            x >>= 1;
        }
        return res - x;
    }
    // Leading zeros
    constexpr int hint_clz(uint64_t x)
    {
        if (x & (uint64_t(0xFFFFFFFF) << 32))
        {
            return hint_clz(uint32_t(x >> 32));
        }
        return hint_clz(uint32_t(x)) + 32;
    }

    // Integer bit length
    template <typename IntTy>
    constexpr int hint_bit_length(IntTy x)
    {
        if (0 == x)
        {
            return 0;
        }
        return sizeof(IntTy) * CHAR_BIT - hint_clz(x);
    }

    // Fast power
    template <typename T, typename T1>
    constexpr T qpow(T m, T1 n)
    {
        T result = 1;
        while (true)
        {
            if (n & 1)
            {
                result *= m;
            }
            if (0 == n)
            {
                break;
            }
            m *= m;
            n >>= 1;
        }
        return result;
    }

    constexpr int hint_popcnt(uint32_t n)
    {
        constexpr uint32_t mask55 = 0x55555555;
        constexpr uint32_t mask33 = 0x33333333;
        constexpr uint32_t mask0f = 0x0f0f0f0f;
        constexpr uint32_t maskff = 0x00ff00ff;
        n = (n & mask55) + ((n >> 1) & mask55);
        n = (n & mask33) + ((n >> 2) & mask33);
        n = (n & mask0f) + ((n >> 4) & mask0f);
        n = (n & maskff) + ((n >> 8) & maskff);
        return uint16_t(n) + (n >> 16);
    }
    constexpr int hint_popcnt(uint64_t n)
    {
        constexpr uint64_t mask5555 = 0x5555555555555555;
        constexpr uint64_t mask3333 = 0x3333333333333333;
        constexpr uint64_t mask0f0f = 0x0f0f0f0f0f0f0f0f;
        constexpr uint64_t mask00ff = 0x00ff00ff00ff00ff;
        constexpr uint64_t maskffff = 0x0000ffff0000ffff;
        n = (n & mask5555) + ((n >> 1) & mask5555);
        n = (n & mask3333) + ((n >> 2) & mask3333);
        n = (n & mask0f0f) + ((n >> 4) & mask0f0f);
        n = (n & mask00ff) + ((n >> 8) & mask00ff);
        n = (n & maskffff) + ((n >> 16) & maskffff);
        return uint32_t(n) + (n >> 32);
    }

    constexpr uint32_t bitrev32(uint32_t n)
    {
        constexpr uint32_t mask55 = 0x55555555;
        constexpr uint32_t mask33 = 0x33333333;
        constexpr uint32_t mask0f = 0x0f0f0f0f;
        constexpr uint32_t maskff = 0x00ff00ff;
        n = ((n & mask55) << 1) | ((n >> 1) & mask55);
        n = ((n & mask33) << 2) | ((n >> 2) & mask33);
        n = ((n & mask0f) << 4) | ((n >> 4) & mask0f);
        n = ((n & maskff) << 8) | ((n >> 8) & maskff);
        return (n << 16) | (n >> 16);
    }
    constexpr uint32_t bitrev(uint32_t n, int len)
    {
        assert(len <= 32);
        return bitrev32(n) >> (32 - len);
    }

    template <typename T>
    void fill_zero(T begin, T end)
    {
        std::memset(&begin[0], 0, (end - begin) * sizeof(T));
    }

    template <typename Float>
    struct Float2
    {
        Float x0, x1;
        using F2 = Float2;
        Float2() = default;
        constexpr Float2(Float x0, Float x1) : x0(x0), x1(x1) {}

        constexpr F2 &operator+=(const F2 &rhs)
        {
            x0 += rhs.x0;
            x1 += rhs.x1;
            return *this;
        }
        constexpr F2 &operator-=(const F2 &rhs)
        {
            x0 -= rhs.x0;
            x1 -= rhs.x1;
            return *this;
        }
        constexpr F2 &operator*=(const F2 &rhs)
        {
            x0 *= rhs.x0;
            x1 *= rhs.x1;
            return *this;
        }
        friend constexpr F2 operator+(const F2 &lhs, const F2 &rhs)
        {
            return F2(lhs.x0 + rhs.x0, lhs.x1 + rhs.x1);
        }
        friend constexpr F2 operator-(const F2 &lhs, const F2 &rhs)
        {
            return F2(lhs.x0 - rhs.x0, lhs.x1 - rhs.x1);
        }
        friend constexpr F2 operator*(const F2 &lhs, const F2 &rhs)
        {
            return F2(lhs.x0 * rhs.x0, lhs.x1 * rhs.x1);
        }
        friend constexpr F2 operator*(const F2 &lhs, const Float &rhs)
        {
            return F2(lhs.x0 * rhs, lhs.x1 * rhs);
        }
        constexpr F2 reverse() const
        {
            return F2(x1, x0);
        }
        constexpr void set1(Float x)
        {
            x0 = x1 = x;
        }
        static constexpr F2 from1(Float x)
        {
            return F2(x, x);
        }
        static constexpr F2 fromMem(const Float *p)
        {
            return F2(p[0], p[1]);
        }
        void store(Float *p) const
        {
            p[0] = x0;
            p[1] = x1;
        }
    };

    template <typename Float>
    struct Complex2
    {
        using F2 = Float2<Float>;
        using C2 = Complex2;
        F2 real, imag;
        Complex2() = default;
        constexpr Complex2(F2 r, F2 i) : real(r), imag(i) {}
        constexpr Complex2(Float r, Float i) : real(F2::from1(r)), imag(F2::from1(i)) {}
        constexpr Complex2(Float x0, Float x1, Float x2, Float x3) : real(x0, x1), imag(x2, x3) {}

        constexpr C2 &operator+=(const C2 &rhs)
        {
            real += rhs.real;
            imag += rhs.imag;
            return *this;
        }
        constexpr C2 &operator-=(const C2 &rhs)
        {
            real -= rhs.real;
            imag -= rhs.imag;
            return *this;
        }
        constexpr C2 &operator*=(const C2 &rhs)
        {
            F2 r = real * rhs.real - imag * rhs.imag;
            F2 i = real * rhs.imag + imag * rhs.real;
            return *this = C2(r, i);
        }
        friend constexpr C2 operator+(const C2 &lhs, const C2 &rhs)
        {
            return C2(lhs.real + rhs.real, lhs.imag + rhs.imag);
        }
        friend constexpr C2 operator-(const C2 &lhs, const C2 &rhs)
        {
            return C2(lhs.real - rhs.real, lhs.imag - rhs.imag);
        }
        friend constexpr C2 operator*(const C2 &lhs, const F2 &rhs)
        {
            return C2(lhs.real * rhs, lhs.imag * rhs);
        }
        friend constexpr C2 operator*(const C2 &lhs, const Float &rhs)
        {
            return C2(lhs.real * rhs, lhs.imag * rhs);
        }
        constexpr C2 mul(const C2 &other) const
        {
            const F2 ii = imag * other.imag;
            const F2 ri = real * other.imag;
            const F2 r = real * other.real - ii;
            const F2 i = imag * other.real + ri;
            return C2(r, i);
        }
        constexpr C2 mulConj(const C2 &other) const
        {
            const F2 ii = imag * other.imag;
            const F2 ri = real * other.imag;
            const F2 r = real * other.real + ii;
            const F2 i = imag * other.real - ri;
            return C2(r, i);
        }
        constexpr C2 reverse() const
        {
            return C2(real.reverse(), imag.reverse());
        }
        constexpr void permute()
        {
            std::swap(real.x1, imag.x0);
        }
        void load(const Float *p)
        {
            real = F2::fromMem(p);
            imag = F2::fromMem(p + 2);
        }
        void store(Float *p) const
        {
            real.store(p);
            imag.store(p + 2);
        }
        void print() const
        {
            std::cout << '(' << real.x0 << ',' << imag.x0 << ") "
                      << '(' << real.x1 << ',' << imag.x1 << ")\n";
        }
    };

    // FFT与类FFT变换的命名空间
    namespace transform
    {

        template <typename T>
        inline void transform2(T &sum, T &diff)
        {
            T temp0 = sum, temp1 = diff;
            sum = temp0 + temp1;
            diff = temp0 - temp1;
        }

        template <typename T>
        inline void transform2(const T a, const T b, T &sum, T &diff)
        {
            sum = a + b;
            diff = a - b;
        }
        namespace fft
        {
            constexpr size_t FFT_MAX_LEN = size_t(1) << 23;

            template <typename Float>
            inline std::complex<Float> getOmega(size_t n, size_t index, Float factor = 1)
            {
                Float theta = -HINT_2PI * index / n;
                return std::polar<Float>(1, theta * factor);
            }
            template <typename Float>
            inline void difSplit(Float &r0, Float &i0, Float &r1, Float &i1, Float &r2, Float &i2, Float &r3, Float &i3)
            {
                transform2(r0, r2);
                transform2(i0, i2);
                transform2(r1, r3);
                transform2(i1, i3);

                transform2(r2, i3);
                transform2(i2, r3, r3, i2);
                std::swap(i3, r3);
            }
            template <typename Float>
            inline void iditSplit(Float &r0, Float &i0, Float &r1, Float &i1, Float &r2, Float &i2, Float &r3, Float &i3)
            {
                transform2(r2, r3);
                transform2(i2, i3);

                transform2(r0, r2);
                transform2(i0, i2);
                transform2(r1, i3, i3, r1);
                transform2(i1, r3);
                std::swap(i3, r3);
            }
            template <typename Float, int DIV>
            struct FFTTable
            {
                using C2 = Complex2<Float>;
                FFTTable(int factor_in) : factor(factor_in), table(8)
                {
                    size_t len = table.size(), rank = len * DIV / 4;
                    auto it = getBegin(rank);
                    Float theta = -HINT_2PI * factor / rank;
                    table[4] = 1, table[6] = 0;
                    table[5] = std::cos(theta), table[7] = std::sin(theta);
                }
                void expandLog(int log_len)
                {
                    expand(size_t(1) << log_len);
                }
                void expand(size_t fft_len)
                {
                    size_t cur_len = table.size() * DIV / 4;
                    if (fft_len <= cur_len)
                    {
                        return;
                    }
                    size_t new_len = fft_len * 4 / DIV;
                    table.resize(new_len);
                    for (size_t rank = cur_len * 2; rank <= fft_len; rank *= 2)
                    {
                        auto it = getBegin(rank), last_it = getBegin(rank / 2);
                        Float theta = -HINT_2PI * factor / rank;
                        C2 unit(std::cos(theta), std::sin(theta));
                        size_t len = rank * 2 / DIV;
                        for (auto end = it + len; it < end; it += 8, last_it += 4)
                        {
                            C2 omega0, omega1;
                            omega0.load(last_it);
                            omega1 = omega0.mul(unit);
                            std::swap(omega0.real.x1, omega1.real.x0);
                            std::swap(omega0.imag.x1, omega1.imag.x0);
                            omega0.store(it);
                            omega1.store(it + 4);
                        }
                    }
                }
                constexpr const Float *getBegin(size_t rank) const
                {
                    return &table[rank * 2 / DIV];
                }
                constexpr Float *getBegin(size_t rank)
                {
                    return &table[rank * 2 / DIV];
                }
                std::vector<Float> table;
                int factor;
            };

            template <typename Float>
            class FFT
            {
                using Table = FFTTable<Float, 4>;
                using F2 = Float2<Float>;
                using C2 = Complex2<Float>;

            public:
                FFT() : table1(1), table3(3) {}
                void expand(size_t float_len)
                {
                    table1.expand(float_len / 2);
                    table3.expand(float_len / 2);
                }
                template <bool RIRI_IN>
                void dif(Float inout[], size_t float_len)
                {
                    if (float_len <= 8)
                    {
                        difSmall<RIRI_IN>(inout, float_len);
                        return;
                    }
                    expand(float_len);
                    const size_t fft_len = float_len / 2, c2_len = fft_len / 2;
                    const size_t stride1 = c2_len / 4, stride2 = stride1 * 2, stride3 = stride1 * 3;
                    auto tp1 = reinterpret_cast<const C2 *>(table1.getBegin(fft_len));
                    auto tp3 = reinterpret_cast<const C2 *>(table3.getBegin(fft_len));
                    auto it = reinterpret_cast<C2 *>(inout);
                    for (auto end = it + stride1; it < end; it++, tp1++, tp3++)
                    {
                        C2 c0 = it[0], c1 = it[stride1], c2 = it[stride2], c3 = it[stride3];
                        if (RIRI_IN)
                        {
                            c0.permute(), c1.permute(), c2.permute(), c3.permute();
                        }
                        difSplit(c0.real, c0.imag, c1.real, c1.imag, c2.real, c2.imag, c3.real, c3.imag);
                        it[0] = c0, it[stride1] = c1, it[stride2] = c2.mul(tp1[0]), it[stride3] = c3.mul(tp3[0]);
                    }
                    size_t stride = float_len / 4;
                    dif<false>(inout, stride * 2);
                    dif<false>(inout + stride * 2, stride);
                    dif<false>(inout + stride * 3, stride);
                }
                template <bool RIRI_OUT>
                void idit(Float inout[], size_t float_len)
                {
                    if (float_len <= 8)
                    {
                        iditSmall<RIRI_OUT>(inout, float_len);
                        return;
                    }
                    expand(float_len);
                    size_t stride = float_len / 4;
                    idit<false>(inout, stride * 2);
                    idit<false>(inout + stride * 2, stride);
                    idit<false>(inout + stride * 3, stride);
                    const size_t fft_len = float_len / 2, c2_len = fft_len / 2;
                    const size_t stride1 = c2_len / 4, stride2 = stride1 * 2, stride3 = stride1 * 3;
                    auto tp1 = reinterpret_cast<const C2 *>(table1.getBegin(fft_len));
                    auto tp3 = reinterpret_cast<const C2 *>(table3.getBegin(fft_len));
                    auto it = reinterpret_cast<C2 *>(inout);
                    for (auto end = it + stride1; it < end; it++, tp1++, tp3++)
                    {
                        C2 c0 = it[0], c1 = it[stride1], c2 = it[stride2].mulConj(tp1[0]), c3 = it[stride3].mulConj(tp3[0]);
                        iditSplit(c0.real, c0.imag, c1.real, c1.imag, c2.real, c2.imag, c3.real, c3.imag);
                        if (RIRI_OUT)
                        {
                            c0.permute(), c1.permute(), c2.permute(), c3.permute();
                        }
                        it[0] = c0, it[stride1] = c1, it[stride2] = c2, it[stride3] = c3;
                    }
                }

                template <bool RIRI_IN>
                void difSmall(Float inout[], size_t float_len)
                {
                    if (float_len <= 2)
                    {
                        return;
                    }
                    auto itc = reinterpret_cast<C2 *>(inout);
                    auto itf = reinterpret_cast<F2 *>(inout);
                    if (float_len == 4) // 2
                    {
                        if (RIRI_IN)
                        {
                            std::swap(inout[1], inout[2]);
                        }
                        transform2(inout[0], inout[1]);
                        transform2(inout[2], inout[3]);
                    }
                    else // 4
                    {
                        if (RIRI_IN)
                        {
                            std::swap(inout[1], inout[2]);
                            std::swap(inout[5], inout[6]);
                        }
                        Float r0 = inout[0], r1 = inout[1], i0 = inout[2], i1 = inout[3];
                        Float r2 = inout[4], r3 = inout[5], i2 = inout[6], i3 = inout[7];
                        difSplit(r0, i0, r1, i1, r2, i2, r3, i3);
                        transform2(r0, r1);
                        transform2(i0, i1);
                        inout[0] = r0, inout[1] = r1, inout[2] = i0, inout[3] = i1;
                        inout[4] = r2, inout[5] = r3, inout[6] = i2, inout[7] = i3;
                    }
                }
                template <bool RIRI_OUT>
                void iditSmall(Float inout[], size_t float_len)
                {
                    if (float_len <= 2)
                    {
                        return;
                    }
                    auto itc = reinterpret_cast<C2 *>(inout);
                    auto itf = reinterpret_cast<F2 *>(inout);
                    if (float_len == 4) // 2
                    {
                        transform2(inout[0], inout[1]);
                        transform2(inout[2], inout[3]);
                        if (RIRI_OUT)
                        {
                            std::swap(inout[1], inout[2]);
                        }
                    }
                    else // 4
                    {
                        Float r0 = inout[0], r1 = inout[1], i0 = inout[2], i1 = inout[3];
                        Float r2 = inout[4], r3 = inout[5], i2 = inout[6], i3 = inout[7];
                        transform2(r0, r1);
                        transform2(i0, i1);
                        iditSplit(r0, i0, r1, i1, r2, i2, r3, i3);
                        inout[0] = r0, inout[1] = r1, inout[2] = i0, inout[3] = i1;
                        inout[4] = r2, inout[5] = r3, inout[6] = i2, inout[7] = i3;
                        if (RIRI_OUT)
                        {
                            std::swap(inout[1], inout[2]);
                            std::swap(inout[5], inout[6]);
                        }
                    }
                }

            private:
                Table table1, table3;
            };

            template <typename Float>
            class BinRevTableComplexIterHP
            {
            public:
                using Complex = std::complex<Float>;
                static constexpr int MAX_LOG_LEN = 32;
                static constexpr size_t MAX_LEN = size_t(1) << MAX_LOG_LEN;

                BinRevTableComplexIterHP(int log_max_iter_in, int log_fft_len_in)
                    : index(0), pop(0), log_max_iter(log_max_iter_in), log_fft_len(log_fft_len_in)
                {
                    assert(log_max_iter <= log_fft_len);
                    assert(log_fft_len <= MAX_LOG_LEN);
                    const Float factor = Float(1) / (size_t(1) << (log_fft_len - log_max_iter));
                    for (int i = 0; i < MAX_LOG_LEN; i++)
                    {
                        units[i] = getOmega<Float>(size_t(1) << (i + 1), 1, factor);
                    }
                    table[0] = Complex(1, 0);
                }
                void reset(size_t i = 0)
                {
                    index = i;
                    if (i == 0)
                    {
                        pop = 0;
                        return;
                    }
                    pop = hint_popcnt(i);
                    const size_t len = size_t(1) << log_fft_len;
                    for (int p = pop; p > 0; p--)
                    {
                        table[p] = getOmega<Float>(len, bitrev(i, log_max_iter));
                        i &= (i - 1);
                    }
                }
                Complex iterate()
                {
                    Complex res = table[pop];
                    index++;
                    int zero = hint_ctz(index);
                    pop -= zero;
                    table[pop + 1] = table[pop] * units[zero];
                    pop++;
                    return res;
                }

            private:
                Complex units[MAX_LOG_LEN]{};
                Complex table[MAX_LOG_LEN]{};
                size_t index;
                int pop;
                int log_max_iter, log_fft_len;
            };

            template <typename Float>
            class BinRevTableC2HP
            {
            public:
                using C1 = std::complex<Float>;
                using C2 = Complex2<Float>;
                static constexpr int MAX_LOG_LEN = 32, LOG_BLOCK = 1, BLOCK = 1 << LOG_BLOCK;
                static constexpr size_t MAX_LEN = size_t(1) << MAX_LOG_LEN;

                BinRevTableC2HP(int log_max_iter_in, int log_fft_len_in)
                    : index(0), pop(0), log_max_iter(log_max_iter_in), log_fft_len(log_fft_len_in)
                {
                    assert(log_max_iter <= log_fft_len);
                    assert(log_fft_len <= MAX_LOG_LEN);
                    const Float factor = Float(1) / (size_t(1) << (log_fft_len - log_max_iter));
                    for (int i = 0; i < MAX_LOG_LEN; i++)
                    {
                        units[i] = getOmega(size_t(1) << (i + 1), 1, factor);
                    }
                    auto fp = reinterpret_cast<Float *>(table);
                    fp[0] = 1, fp[BLOCK] = 0;
                    for (int i = 1; i < BLOCK; i++)
                    {
                        C1 omega = getOmega(BLOCK, bitrev(i, LOG_BLOCK), factor);
                        fp[i] = omega.real(), fp[i + BLOCK] = omega.imag();
                    }
                }

                // Only for power of 2
                void reset(size_t i = 0)
                {
                    if (i == 0)
                    {
                        pop = 0, index = i;
                        return;
                    }
                    assert((i & (i - 1)) == 0);
                    assert(i % BLOCK == 0);
                    pop = 1, index = i / BLOCK;
                    int zero = hint_ctz(index);
                    auto fp = reinterpret_cast<Float *>(&units[zero + 1]);
                    table[1].real.set1(fp[0]);
                    table[1].imag.set1(fp[1]);
                    table[1] = table[1].mul(table[0]);
                }
                C2 iterate()
                {
                    C2 res = table[pop], unitx;
                    index++;
                    int zero = hint_ctz(index);
                    auto fp = reinterpret_cast<Float *>(&units[zero + 1]);
                    unitx.real.set1(fp[0]);
                    unitx.imag.set1(fp[1]);
                    pop -= zero;
                    table[pop + 1] = table[pop].mul(unitx);
                    pop++;
                    return res;
                }

            private:
                C1 units[MAX_LOG_LEN]{};
                C2 table[MAX_LOG_LEN]{};
                size_t index;
                int pop;
                int log_max_iter, log_fft_len;
            };

            template <size_t RI_DIFF = 1, typename Float>
            inline void dot_rfft(Float *inout0, Float *inout1, const Float *in0, const Float *in1,
                                 const std::complex<Float> &omega0, const Float factor = 1)
            {
                using Complex = std::complex<Float>;
                auto mul1 = [](Complex c0, Complex c1)
                {
                    return Complex(c0.imag() * c1.real() + c0.real() * c1.imag(),
                                   c0.imag() * c1.imag() - c0.real() * c1.real());
                };
                auto mul2 = [](Complex c0, Complex c1)
                {
                    return Complex(c0.real() * c1.imag() - c0.imag() * c1.real(),
                                   c0.real() * c1.real() + c0.imag() * c1.imag());
                };
                auto compute2 = [&omega0](Complex in0, Complex in1, Complex &out0, Complex &out1, auto Func)
                {
                    in1 = std::conj(in1);
                    transform2(in0, in1);
                    in1 = Func(in1, omega0);
                    out0 = in0 + in1;
                    out1 = std::conj(in0 - in1);
                };
                Complex c0, c1;
                {
                    Complex x0, x1, x2, x3;
                    c0.real(inout0[0]), c0.imag(inout0[RI_DIFF]), c1.real(inout1[0]), c1.imag(inout1[RI_DIFF]);
                    compute2(c0, c1, x0, x1, mul1);
                    c0.real(in0[0]), c0.imag(in0[RI_DIFF]), c1.real(in1[0]), c1.imag(in1[RI_DIFF]);
                    compute2(c0, c1, x2, x3, mul1);
                    x0 *= x2 * factor;
                    x1 *= x3 * factor;
                    compute2(x0, x1, c0, c1, mul2);
                }
                inout0[0] = c0.real(), inout0[RI_DIFF] = c0.imag();
                inout1[0] = c1.real(), inout1[RI_DIFF] = c1.imag();
            }
            template <typename Float>
            inline void dot_rfftX2(Float *inout0, Float *inout1, const Float *in0, const Float *in1, const Complex2<Float> &omega0, const Float2<Float> &inv)
            {
                using C2 = Complex2<Float>;
                auto mul1 = [](C2 c0, C2 c1)
                {
                    return C2(c0.imag * c1.real + c0.real * c1.imag,
                              c0.imag * c1.imag - c0.real * c1.real);
                };
                auto mul2 = [](C2 c0, C2 c1)
                {
                    return C2(c0.real * c1.imag - c0.imag * c1.real,
                              c0.real * c1.real + c0.imag * c1.imag);
                };
                auto compute2 = [&omega0](C2 c0, C2 c1, C2 &out0, C2 &out1, auto Func)
                {
                    C2 t0(c0.real + c1.real, c0.imag - c1.imag), t1(c0.real - c1.real, c0.imag + c1.imag);
                    t1 = Func(t1, omega0);
                    out0 = t0 + t1;
                    out1.real = t0.real - t1.real;
                    out1.imag = t1.imag - t0.imag;
                };
                C2 c0, c1;
                {
                    C2 x0, x1, x2, x3;
                    c0.load(inout0), c1.load(inout1);
                    compute2(c0, c1.reverse(), x0, x1, mul1);

                    c0.load(in0), c1.load(in1);
                    compute2(c0, c1.reverse(), x2, x3, mul1);
                    c0 = x0.mul(x2) * inv;
                    c1 = x1.mul(x3) * inv;
                    compute2(c0, c1, c0, c1, mul2);
                }
                c0.store(inout0), c1.reverse().store(inout1);
            }
            // inv = 1 / float_len
            template <size_t RI_DIFF = 1, typename Float>
            inline void real_dot_binrev(Float in_out[], Float in[], size_t float_len, Float inv = -1)
            {
                static_assert(is_2pow(RI_DIFF));
                assert(is_2pow(float_len));
                assert(float_len >= RI_DIFF * 2);
                auto transToRIRI = [](Float arr[], size_t len)
                {
                    if (RI_DIFF == 1)
                    {
                        return;
                    }
                    Float temp[RI_DIFF * 2]{};
                    for (auto it = arr, end = arr + len; it < end; it += RI_DIFF * 2)
                    {
                        std::copy(it, it + RI_DIFF * 2, temp);
                        for (size_t i = 0; i < RI_DIFF; i++)
                        {
                            it[i * 2] = temp[i];
                            it[i * 2 + 1] = temp[i + RI_DIFF];
                        }
                    }
                };
                auto transToRRII = [](Float arr[], size_t len)
                {
                    if (RI_DIFF == 1)
                    {
                        return;
                    }
                    Float temp[RI_DIFF * 2]{};
                    for (auto it = arr, end = arr + len; it < end; it += RI_DIFF * 2)
                    {
                        for (size_t i = 0; i < RI_DIFF; i++)
                        {
                            temp[i] = it[i * 2];
                            temp[i + RI_DIFF] = it[i * 2 + 1];
                        }
                        std::copy(temp, temp + RI_DIFF * 2, it);
                    }
                };
                transToRIRI(in_out, float_len);
                if (in_out != in)
                {
                    transToRIRI(in, float_len);
                }
                using Complex = std::complex<Float>;
                inv = inv < 0 ? Float(2) / float_len : inv * Float(2);
                {
                    auto r0 = in_out[0], i0 = in_out[1], r1 = in[0], i1 = in[1];
                    transform2(r0, i0);
                    transform2(r1, i1);
                    r0 *= r1, i0 *= i1;
                    transform2(r0, i0);
                    in_out[0] = r0 * 0.5 * inv, in_out[1] = i0 * 0.5 * inv;
                    auto temp = Complex(in_out[2], in_out[3]) * Complex(in[2], in[3]) * inv;
                    in_out[2] = temp.real(), in_out[3] = temp.imag();
                    inv /= Float(8);
                    dot_rfft(&in_out[4], &in_out[6], &in[4], &in[6], Complex(COS_PI_8, -COS_PI_8), inv);
                }
                BinRevTableComplexIterHP<Float> table(31, 32);
                for (size_t begin = 8; begin < float_len; begin *= 2)
                {
                    table.reset(begin / 2);
                    auto it0 = in_out + begin, it1 = it0 + begin - 2, it2 = in + begin, it3 = it2 + begin - 2;
                    for (; it0 < it1; it0 += 2, it1 -= 2, it2 += 2, it3 -= 2)
                    {
                        dot_rfft(it0, it1, it2, it3, table.iterate(), inv);
                    }
                }
                transToRRII(in_out, float_len);
            }

            template <typename Float>
            inline void real_dot_binrev2(Float in_out[], Float in[], size_t float_len)
            {
                using Complex = std::complex<Float>;
                using F2 = Float2<Float>;
                Float inv = 1.0 / float_len;
                real_dot_binrev<2>(in_out, in, 16, inv);
                inv = 0.25 / float_len;
                const F2 invx = F2::from1(inv);
                BinRevTableC2HP<Float> table(31, 32);
                for (size_t begin = 16; begin < float_len; begin *= 2)
                {
                    table.reset(begin / 2);
                    auto it0 = in_out + begin, it1 = it0 + begin - 4, it2 = in + begin, it3 = it2 + begin - 4;
                    for (; it0 < it1; it0 += 4, it1 -= 4, it2 += 4, it3 -= 4)
                    {
                        dot_rfftX2(it0, it1, it2, it3, table.iterate(), invx);
                    }
                }
            }

            template <typename Float>
            inline void real_conv(Float *in_out1, Float *in2, size_t float_len)
            {
                assert(is_2pow(float_len));
                assert(float_len <= FFT_MAX_LEN * 2);
                static FFT<Float> fft;
                fft.expand(float_len);
                fft.template dif<true>(in_out1, float_len);
                if (in_out1 != in2)
                {
                    fft.template dif<true>(in2, float_len);
                }
                real_dot_binrev2(in_out1, in2, float_len);
                fft.template idit<true>(in_out1, float_len);
            }
        }
    }
    constexpr size_t count_base10(uint64_t num)
    {
        size_t count = 0;
        while (num)
        {
            num /= 10;
            count++;
        }
        return count;
    }
    constexpr uint16_t str4toi(const char *s)
    {
        return s[0] * 1000 + s[1] * 100 + s[2] * 10 + s[3] - '0' * 1111;
    }
    constexpr void itostr4(uint16_t n, char *s)
    {
        s[0] = n / 1000 + '0';
        s[1] = n / 100 % 10 + '0';
        s[2] = n / 10 % 10 + '0';
        s[3] = n % 10 + '0';
    }
    template <typename T>
    struct ViewTy
    {
        const T *ptr;
        size_t size;
        ViewTy() = default;
        ViewTy(const T *ptr, size_t size) : ptr(ptr), size(size) {}
        const T &operator[](size_t index) const
        {
            return ptr[index];
        }
        ViewTy operator+(size_t offset) const
        {
            assert(offset <= size);
            return ViewTy{ptr + offset, size - offset};
        }
        const T *begin() const
        {
            return ptr;
        }
        const T *end() const
        {
            return ptr + size;
        }
    };
    template <typename T>
    struct SpanTy
    {
        T *ptr;
        size_t size;
        SpanTy() = default;
        SpanTy(T *ptr, size_t size) : ptr(ptr), size(size) {}
        const T &operator[](size_t index) const
        {
            return ptr[index];
        }
        T &operator[](size_t index)
        {
            return ptr[index];
        }
        operator ViewTy<T>()
        {
            return ViewTy<T>{ptr, size};
        }
        SpanTy operator+(size_t offset) const
        {
            assert(offset <= size);
            return SpanTy{ptr + offset, size - offset};
        }
        const T *begin() const
        {
            return ptr;
        }
        const T *end() const
        {
            return ptr + size;
        }
        T *begin()
        {
            return ptr;
        }
        T *end()
        {
            return ptr + size;
        }
    };

    template <typename T>
    T add_half(T a, T b, T base, bool &cf)
    {
        a += b;
        cf = a >= base;
        const T mask = T(0) - T(cf);
        return a - (base & mask);
    }
    template <typename T>
    T sub_half(T a, T b, T base, bool &bf)
    {
        bf = a < b;
        const T mask = T(0) - T(bf);
        return a - b + (base & mask);
    }

    template <typename T>
    constexpr size_t count_ture_length(const T array[], size_t length)
    {
        if (nullptr == array)
        {
            return 0;
        }
        while (length > 0 && array[length - 1] == 0)
        {
            length--;
        }
        return length;
    }

    class Integer
    {
    public:
        using Limb = uint16_t;
        using Limb2 = uint32_t;
        using DataVec = std::vector<Limb>;
        using Span = SpanTy<Limb>;
        using View = ViewTy<Limb>;
        static constexpr Limb BASE_DIGIT = 4;
        static constexpr Limb BASE = qpow(10, BASE_DIGIT);
        static constexpr Limb HALF_BASE = BASE / 2;
        Integer() : data(), sign(false) {}
        // Integer 拷贝构造
        Integer(const Integer &input) = default;
        // Integer 移动构造
        Integer(Integer &&input) = default;
        // string 参数构造
        Integer(const std::string &input) : sign(false)
        {
            fromString(input);
        }
        Integer(const char *input) : sign(false)
        {
            fromString(input);
        }
        Integer(View input) : sign(false), data(input.begin(), input.end())
        {
            removeLeadingZero();
        }
        Integer(Span input) : sign(false), data(input.begin(), input.end())
        {
            removeLeadingZero();
        }
        // 通用构造
        template <typename T>
        Integer(const T &input)
        {
            sign = input < 0;
            uint64_t num = std::abs(input);
            while (num > 0)
            {
                data.push_back(num % BASE);
                num /= BASE;
            }
        }
        // Integer 拷贝赋值
        Integer &operator=(const Integer &input) = default;
        // Integer 移动赋值
        Integer &operator=(Integer &&input) = default;

        View getView() const
        {
            return View{data.data(), data.size()};
        }
        Span getSpan()
        {
            return Span{data.data(), data.size()};
        }

        bool isOdd() const
        {
            if (length() == 0)
            {
                return false;
            }
            return data[0] % 2 == 1;
        }
        bool isEven() const
        {
            return !isOdd();
        }
        bool isZero() const
        {
            return length() == 0;
        }
        // 更改符号
        void setSign(bool new_sign)
        {
            sign = new_sign;
        }
        // 是否为负号
        bool isNeg() const
        {
            return sign && (length() > 0);
        }
        size_t length() const
        {
            return data.size();
        }
        size_t lengthBase10() const
        {
            size_t len = length();
            if (len == 0)
            {
                return 1;
            }
            return (len - 1) * BASE_DIGIT + count_base10(data[len - 1]);
        }
        void removeLeadingZero()
        {
            size_t len = length();
            len = count_ture_length(data.data(), len);
            data.resize(len);
            sign = sign && (len > 0);
        }
        void clear()
        {
            data.clear();
            sign = false;
        }
        void fromString(const std::string &str)
        {
            if (str.empty())
            {
                return;
            }
            auto p_begin = str.data(), p_end = p_begin + str.size();
            if (str[0] == '-')
            {
                sign = true;
                p_begin++;
            }
            size_t len = p_end - p_begin;
            data.resize((len + BASE_DIGIT - 1) / BASE_DIGIT);
            size_t i = 0;
            while (p_end > p_begin + 3)
            {
                p_end -= BASE_DIGIT;
                data[i] = str4toi(p_end);
                i++;
            }
            if (p_end > p_begin)
            {
                data[i] = 0;
                while (p_end > p_begin)
                {
                    data[i] *= 10;
                    data[i] += p_begin[0] - '0';
                    p_begin++;
                }
            }
            removeLeadingZero();
        }
        std::string toString() const
        {
            std::string res;
            std::vector<char> buf(4);
            if (isZero())
            {
                res = "0";
            }
            else
            {
                if (isNeg())
                {
                    res = '-';
                }
                res += std::to_string(data.back());
                size_t i = data.size() - 1;
                while (i > 0)
                {
                    i--;
                    itostr4(data[i], buf.data());
                    res.append(buf.data(), 4);
                }
            }
            return res;
        }
        operator std::string() const
        {
            return toString();
        }
        void print() const
        {
            std::cout << toString() << std::endl;
        }
        friend std::istream &operator>>(std::istream &is, Integer &num)
        {
            std::string tmp;
            is >> tmp;
            num.fromString(tmp);
            return is;
        }
        friend std::ostream &operator<<(std::ostream &os, const Integer &num)
        {
            return os << num.toString();
        }
        static int absCompare(View input1, View input2)
        {
            size_t len1 = count_ture_length(input1.ptr, input1.size);
            size_t len2 = count_ture_length(input2.ptr, input2.size);
            if (len1 != len2)
            {
                return len1 > len2 ? 1 : -1;
            }
            size_t i = len1;
            while (i > 0)
            {
                i--;
                if (input1[i] != input2[i])
                {
                    return input1[i] > input2[i] ? 1 : -1;
                }
            }
            return 0;
        }
        static bool absAdd(View in1, View in2, Span out)
        {
            if (in1.size < in2.size)
            {
                std::swap(in1, in2);
            }
            size_t i = 0;
            bool carry = 0;
            for (; i < in2.size; i++)
            {
                out[i] = add_half<Limb>(in1[i], in2[i] + carry, BASE, carry);
            }
            for (; i < in1.size; i++)
            {
                out[i] = add_half<Limb>(in1[i], carry, BASE, carry);
            }
            return carry;
        }
        static bool absSub(View in1, View in2, Span out)
        {
            assert(in1.size >= in2.size);
            size_t i = 0;
            bool borrow = 0;
            for (; i < in2.size; i++)
            {
                out[i] = sub_half<Limb>(in1[i], in2[i] + borrow, BASE, borrow);
            }
            for (; i < in1.size; i++)
            {
                out[i] = sub_half<Limb>(in1[i], borrow, BASE, borrow);
            }
            return borrow;
        }
        static bool absAdd1(View in1, Limb in2, Span out)
        {
            assert(in1.size > 0);
            bool carry = 0;
            out[0] = add_half<Limb>(in1[0], in2, BASE, carry);
            for (size_t i = 1; i < in1.size; i++)
            {
                out[i] = add_half<Limb>(in1[i], carry, BASE, carry);
            }
            return carry;
        }
        static bool absSub1(View in1, Limb in2, Span out)
        {
            assert(in1.size > 0);
            bool borrow = 0;
            out[0] = sub_half<Limb>(in1[0], in2, BASE, borrow);
            for (size_t i = 1; i < in1.size; i++)
            {
                out[i] = sub_half<Limb>(in1[i], borrow, BASE, borrow);
            }
            return borrow;
        }
        friend bool operator>(const Integer &input1, const Integer &input2)
        {
            if (input1.isNeg() != input2.isNeg())
            {
                return input2.isNeg();
            }
            return (absCompare(input1.getView(), input2.getView()) > 0) != input1.isNeg();
        }
        friend bool operator<(const Integer &input1, const Integer &input2)
        {
            return input2 > input1;
        }
        friend bool operator>=(const Integer &input1, const Integer &input2)
        {
            return !(input1 < input2);
        }
        friend bool operator<=(const Integer &input1, const Integer &input2)
        {
            return !(input1 > input2);
        }
        friend bool operator==(const Integer &input1, const Integer &input2)
        {
            if (input1.isNeg() != input2.isNeg())
            {
                return false;
            }
            return absCompare(input1.getView(), input2.getView()) == 0;
        }
        friend bool operator!=(const Integer &input1, const Integer &input2)
        {
            return !(input1 == input2);
        }
        Integer &add(View input, bool in_sign)
        {
            size_t len1 = this->length(), len2 = input.size;
            if (this->isNeg() == in_sign) // 是否同号
            {
                size_t add_len = std::max(len1, len2) + 1;
                this->data.resize(add_len);
                this->data[add_len - 1] = absAdd(this->getView(), input, this->getSpan());
            }
            else
            {
                size_t sub_len = std::max(len1, len2);
                int cmp = absCompare(this->getView(), input);
                if (cmp > 0)
                {
                    this->data.resize(sub_len);
                    // 不改变符号
                    absSub(this->getView(), input, this->getSpan());
                }
                else if (cmp < 0)
                {
                    this->data.resize(sub_len);
                    this->setSign(in_sign);
                    absSub(input, this->getView(), this->getSpan());
                }
                else
                {
                    this->data.clear();
                }
            }
            this->removeLeadingZero();
            return *this;
        }
        static void basicMul(View in1, View in2, Span out)
        {
            if (in1.size > in2.size)
            {
                std::swap(in1, in2);
            }
            if (in1.size == 0)
            {
                return;
            }
            std::vector<Limb> buf(in1.size + in2.size);
            Limb carry = 0, x = in1[0];
            for (size_t j = 0; j < in2.size; j++)
            {
                Limb2 prod = Limb2(in2[j]) * x + carry;
                buf[j] = prod % BASE;
                carry = prod / BASE;
            }
            buf[in2.size] = carry;
            for (size_t i = 1; i < in1.size; i++)
            {
                x = in1[i], carry = 0;
                for (size_t j = 0; j < in2.size; j++)
                {
                    Limb2 prod = Limb2(in2[j]) * x + carry + buf[i + j];
                    buf[i + j] = prod % BASE;
                    carry = prod / BASE;
                }
                buf[i + in2.size] = carry;
            }
            std::copy(buf.begin(), buf.end(), out.begin());
        }
        static void fftMul(View in1, View in2, Span out)
        {
            size_t len1 = in1.size, len2 = in2.size;
            size_t conv_len = len1 + len2 - 1, float_len = int_ceil2(conv_len);
            std::vector<double> v1(float_len), v2(float_len);
            std::copy(in1.begin(), in1.end(), v1.begin());
            std::copy(in2.begin(), in2.end(), v2.begin());
            transform::fft::real_conv(v1.data(), v2.data(), float_len);
            uint64_t carry = 0;
            for (size_t i = 0; i < conv_len; i++)
            {
                carry += uint64_t(v1[i] + 0.5);
                out[i] = carry % BASE;
                carry /= BASE;
            }
            out[conv_len] = carry;
        }
        static void fftSqr(View in, Span out)
        {
            size_t len = in.size;
            size_t conv_len = len * 2 - 1, float_len = int_ceil2(conv_len);
            std::vector<double> v(float_len);
            std::copy(in.begin(), in.end(), v.begin());
            transform::fft::real_conv(v.data(), v.data(), float_len);
            uint64_t carry = 0;
            for (size_t i = 0; i < conv_len; i++)
            {
                carry += uint64_t(v[i] + 0.5);
                out[i] = carry % BASE;
                carry /= BASE;
            }
            out[conv_len] = carry;
        }
        static void absSqr(View in, Span out)
        {
            assert(out.size >= in.size * 2);
            if (in.size <= 64)
            {
                basicMul(in, in, out);
            }
            else
            {
                fftSqr(in, out);
            }
        }
        static void absMul(View in1, View in2, Span out)
        {
            assert(out.size >= in1.size + in2.size);
            if (in1.ptr == in2.ptr)
            {
                absSqr(in1, out);
                return;
            }
            if (std::min(in1.size, in2.size) <= 64)
            {
                basicMul(in1, in2, out);
            }
            else
            {
                fftMul(in1, in2, out);
            }
        }
        Integer &square()
        {
            this->setSign(false);
            size_t len = this->length();
            this->data.resize(len * 2);
            absSqr(this->getView(), this->getSpan());
            return *this;
        }
        static Limb absMul1(View in, Limb x, Span out)
        {
            Limb carry = 0;
            for (size_t i = 0; i < in.size; i++)
            {
                Limb2 prod = Limb2(in[i]) * x + carry;
                out[i] = prod % BASE;
                carry = prod / BASE;
            }
            return carry;
        }
        static Limb absDiv1(View in, Limb x, Span out)
        {
            Limb rem = 0;
            size_t i = in.size;
            while (i > 0)
            {
                i--;
                Limb2 prod = Limb2(in[i]) + Limb2(rem) * BASE;
                out[i] = prod / x;
                rem = prod % x;
            }
            return rem;
        }
        Limb selfDivRem1(Limb x)
        {
            Limb rem = absDiv1(this->getView(), x, this->getSpan());
            this->removeLeadingZero();
            return rem;
        }
        static void absDivBasicCore(Span dividend, View divisor, Span quotient)
        {
            if (dividend.size <= divisor.size)
            {
                return;
            }
            assert(divisor.size > 0);
            size_t len1 = dividend.size, len2 = divisor.size;
            Limb divisor_high = divisor[len2 - 1];
            assert(divisor_high >= HALF_BASE);
            size_t quot_idx = len1 - len2;
            std::vector<Limb> prod(len2 + 1);
            while (quot_idx > 0)
            {
                quot_idx--;
                len1 = quot_idx + len2;
                Limb high1 = dividend[len1], high2 = dividend[len1 - 1], qhat = 0;
                // 被除数前两位除以除数最高位估商
                if (high1 >= divisor_high)
                {
                    qhat = BASE - 1;
                }
                else
                {
                    Limb2 high = Limb2(high1) * BASE + high2;
                    qhat = high / divisor_high;
                }
                Span prod_span(prod.data(), prod.size());
                prod_span[len2] = absMul1(divisor, qhat, prod_span);
                if (prod_span[len2] == 0)
                {
                    prod_span.size = len2;
                }
                Span dividend_span(dividend + quot_idx);
                int count = 0;
                while (absCompare(View(prod_span), View(dividend_span)) > 0)
                {
                    assert(count < 2);
                    count++;
                    auto bf = absSub(prod_span, divisor, prod_span);
                    qhat--;
                    assert(!bf);
                }
                auto bf = absSub(dividend_span, prod_span, dividend_span);
                assert(!bf);
                quotient[quot_idx] = qhat;
                dividend.size = len1;
            }
        }

// k = m.length() = log(BASE,m) + 1, inv = BASE ^ (k * 2) / m
static void absInvNewton(View m, Span inv)
{
    size_t k = m.size;
    assert(inv.size >= k + 1); // 确保内存空间足够
    size_t s = (k - 1) / 2;
    if (s <= 8)
    {
        Limb b_2k[64]{};
        b_2k[k * 2] = 1; // BASE ^ (k * 2)
        absDivBasicCore(Span(b_2k, k * 2 + 1), m, inv);
        return;
    }
    // 计算高位的倒数，即低精度倒数
    absInvNewton(m + s, inv);    // 利用指针移位进行截取
    size_t inv0_len = k - s + 1; // 低精度的inv长度为m'长度加1
    Span inv0(inv.ptr, inv0_len);
    std::vector<Limb> prod(inv0_len * 2 + k); // 计算 inv0 ^ 2 * m, 预留内存空间
    std::vector<Limb> inv2(k + 1);            // 存储 inv0 * 2 * BASE ^ s 所需长度为k - s + 1 + s = k + 1
    Span prod_span(prod.data(), prod.size()), inv2_span(inv2.data(), inv2.size());
    bool cf = absAdd(inv0, inv0, inv2_span + s); // 利用指针移位实现乘 BASE ^ s
    assert(!cf);                                 // 可以证明inv0 * 2的位数和inv0相同, 不会溢出
    absSqr(inv0, prod_span);                     // 计算 inv0 ^ 2
    absMul(View(prod.data(), inv0_len * 2), m, prod_span);
    prod_span = prod_span + 2 * (k - s);        // 右移 k - s 位
    assert(prod_span[prod_span.size - 1] == 0); // 可以证明 inv0 ^ 2 * m 长度不超过 k + 1
    prod_span.size--;                           // 可得 inv0 ^ 2 * m / BASE ^ (k - s) 整数部分长度为 k + 1 和 inv0 * 2 * BASE ^ s 相同
    absSub(inv2_span, prod_span, inv);          // inv = inv0 * 2 * BASE ^ s - inv0 ^ 2 * m / BASE ^ (k - s)
}
static void absDivNewtonCore(Span dividend, View divisor, Span quotient)
{
    if (dividend.size <= divisor.size)
    {
        return;
    }
    assert(divisor.size > 0);
    size_t len1 = dividend.size, len2 = divisor.size;
    Limb divisor_high = divisor[len2 - 1];
    assert(divisor_high >= HALF_BASE);
    std::vector<Limb> inv(len2 + 1);
    Span inv_span(inv.data(), inv.size());
    absInvNewton(divisor, inv_span);
    auto div_seg = [&](Span divid, Span quot)
    {
        if (divid.size <= divisor.size)
        {
            return;
        }
        assert(divid.size <= divisor.size * 2);
        size_t k = divisor.size;
        Span divid_high = divid + (k - 1);
        std::vector<Limb> qhat(divid_high.size + inv_span.size);
        std::vector<Limb> prod(qhat.size() - 1); // 存储 qhat * divisor
        Span qhat_span(qhat.data(), qhat.size()), prod_span(prod.data(), prod.size());
        absMul(inv_span, divid_high, qhat_span); // 被除数乘以倒数
        qhat_span = qhat_span + (k + 1);         // 右移k + 1位
        absMul(divisor, qhat_span, prod_span);   // qhat * divisor
        prod_span.size = count_ture_length(prod_span.ptr, prod_span.size);
        // 比较 qhat * divisor 和 divid大小以进行修正
        while (absCompare(prod_span, divid) > 0)
        {
            absSub(prod_span, divisor, prod_span); // prod -= divisor
            absSub1(qhat_span, 1, qhat_span);      // qhat--
        }
        absSub(divid, prod_span, divid); // divid -= prod
        divid.size = k;
        while (absCompare(divid, divisor) >= 0)
        {
            absSub(divid, divisor, divid);
            absAdd1(qhat_span, 1, qhat_span);
        }
        assert(qhat_span[qhat_span.size - 1] == 0);
        qhat_span.size--;
        std::copy(qhat_span.begin(), qhat_span.end(), quot.begin());
    };
    size_t blocks = len1 / len2, len1_rem = len2 * blocks;
    auto divid_it = dividend.ptr + (len1_rem - len2);
    auto quot_it = quotient.ptr + (len1_rem - len2);
    // 分段进行除法运算, 处理被除数长度远大于除数的情况
    div_seg(dividend + (len1_rem - len2), quotient + (len1_rem - len2));
    while (divid_it > dividend.ptr)
    {
        divid_it -= len2;
        quot_it -= len2;
        div_seg(Span(divid_it, len2 * 2), Span(quot_it, len2));
    }
}
        void absDivRem(const Integer &divisor, Integer &quotient, Integer &remainder) const
        {
            size_t len1 = this->length(), len2 = divisor.length();
            int cmp = absCompare(this->getView(), divisor.getView());
            if (cmp == 0)
            {
                quotient = Limb(1);
                remainder = Limb(0);
            }
            else if (cmp < 0)
            {
                quotient = Limb(0);
                remainder = divisor;
            }
            else if (len2 == 1)
            {
                quotient = *this;
                remainder = quotient.selfDivRem1(divisor.data[0]);
            }
            else
            {
                // 规范化
                Limb factor = divisorNormalizeFactor(divisor.getView());
                Integer dividend_norm = (*this) * factor, divisor_norm = divisor * factor;
                size_t len1 = dividend_norm.length(), len2 = divisor_norm.length();
                assert(len2 == divisor.length());
                size_t quot_len = len1 - len2 + 1;
                quotient.data.resize(quot_len);
                Span divident_span = dividend_norm.getSpan(), divisor_span = divisor_norm.getSpan();
                Span high = divident_span + (quot_len - 1); // 高len2位
                if (absCompare(View(high), View(divisor_span)) >= 0)
                {
                    quotient.data[quot_len - 1] = 1;
                    absSub(high, divisor_span, high);
                }
                // 剩余的quotient一定为len1-len2位
                // absDivBasicCore(divident_span, divisor_span, quotient.getSpan());
                absDivNewtonCore(divident_span, divisor_span, quotient.getSpan());
                dividend_norm.removeLeadingZero();
                Limb rem = dividend_norm.selfDivRem1(factor);
                assert(rem == 0);
                remainder = std::move(dividend_norm);
                quotient.removeLeadingZero();
            }
        }
        static Limb divisorNormalizeFactor(View divisor)
        {
            assert(divisor.size > 0);
            constexpr int HALF_BASE_BITS = hint_bit_length<uint32_t>(HALF_BASE);
            Limb high_limb = divisor[divisor.size - 1];
            if (high_limb >= HALF_BASE)
            {
                return 1;
            }
            int bits = hint_bit_length<uint32_t>(high_limb);
            int shift = HALF_BASE_BITS - bits;
            Limb2 new_high = high_limb << shift;
            if (divisor.size >= 2)
            {
                new_high += Limb2(divisor[divisor.size - 2] << shift) / BASE;
            }
            if (new_high < HALF_BASE)
            {
                shift++;
            }
            else if (new_high >= BASE)
            {
                shift--;
            }
            return Limb(1) << shift;
        }

        Integer &operator+=(const Integer &input)
        {
            return this->add(input.getView(), input.isNeg());
        }
        Integer &operator-=(const Integer &input)
        {
            return this->add(input.getView(), !input.isNeg());
        }
        Integer &operator*=(const Integer &input)
        {
            if (input.isZero() || this->isZero())
            {
                this->clear();
            }
            else
            {
                size_t len1 = this->length(), len2 = input.length();
                this->data.resize(len1 + len2);
                absMul(Span(this->data.data(), len1), input.getView(), this->getSpan());
            }
            return *this;
        }
        Integer &operator*=(Limb input)
        {
            if (input == 0)
            {
                this->clear();
            }
            else if (input > 1)
            {
                assert(input < BASE);
                Limb carry = absMul1(this->getSpan(), input, this->getSpan());
                if (carry > 0)
                {
                    this->data.push_back(carry);
                }
            }
            this->removeLeadingZero();
            return *this;
        }
        Integer &operator/=(const Integer &input)
        {
            Integer quotient, remainder;
            this->absDivRem(input, quotient, remainder);
            *this = std::move(quotient);
            return *this;
        }
        Integer &operator%=(const Integer &input)
        {
            Integer quotient, remainder;
            this->absDivRem(input, quotient, remainder);
            *this = std::move(remainder);
            return *this;
        }

        friend Integer operator+(Integer lhs, const Integer &rhs)
        {
            return lhs += rhs;
        }
        friend Integer operator-(Integer lhs, const Integer &rhs)
        {
            return lhs -= rhs;
        }
        friend Integer operator*(Integer lhs, const Integer &rhs)
        {
            return lhs *= rhs;
        }
        friend Integer operator/(Integer lhs, const Integer &rhs)
        {
            return lhs /= rhs;
        }
        friend Integer operator%(Integer lhs, const Integer &rhs)
        {
            return lhs %= rhs;
        }

        friend Integer operator*(Integer lhs, Limb rhs)
        {
            if (rhs == 0)
            {
                return Integer(0);
            }
            if (rhs > 1)
            {
                assert(rhs < BASE);
                Span lhs_span = lhs.getSpan();
                Limb carry = absMul1(lhs_span, rhs, lhs_span);
                if (carry != 0)
                {
                    lhs.data.push_back(carry);
                }
            }
            lhs.removeLeadingZero();
            return lhs;
        }

    private:
        DataVec data;
        bool sign;
    };
}