#include <complex>
#include <future>
#include <iostream>
#include <random>
#include <stack>
#include <string>
#include <thread>
#include <tuple>
#include <cassert>
#include <climits>
#include <cmath>
#include <cstdlib>
#include <cstring>

#ifndef HINT_MATH_HPP
#define HINT_MATH_HPP
#define MULTITHREAD 0   // 多线程 0 means no, 1 means yes
#define TABLE_TYPE 1    // 复数表的类型 0 means ComplexTable, 1 means ComplexTableX
#define TABLE_PRELOAD 1 // 是否提前初始化表 0 means no, 1 means yes

namespace hint
{
    using UINT_8 = uint8_t;
    using UINT_16 = uint16_t;
    using UINT_32 = uint32_t;
    using UINT_64 = uint64_t;
    using INT_32 = int32_t;
    using INT_64 = int64_t;
    using ULONG = unsigned long;
    using LONG = long;
    using HintFloat = double;
    using Complex = std::complex<HintFloat>;

    constexpr UINT_64 HINT_CHAR_BIT = 8;
    constexpr UINT_64 HINT_SHORT_BIT = 16;
    constexpr UINT_64 HINT_INT_BIT = 32;
    constexpr UINT_64 HINT_INT8_0XFF = UINT8_MAX;
    constexpr UINT_64 HINT_INT8_0X10 = (UINT8_MAX + 1ull);
    constexpr UINT_64 HINT_INT16_0XFF = UINT16_MAX;
    constexpr UINT_64 HINT_INT16_0X10 = (UINT16_MAX + 1ull);
    constexpr UINT_64 HINT_INT32_0XFF = UINT32_MAX;
    constexpr UINT_64 HINT_INT32_0X01 = 1;
    constexpr UINT_64 HINT_INT32_0X80 = 0X80000000ull;
    constexpr UINT_64 HINT_INT32_0X7F = INT32_MAX;
    constexpr UINT_64 HINT_INT32_0X10 = (UINT32_MAX + 1ull);
    constexpr UINT_64 HINT_INT64_0X80 = INT64_MIN;
    constexpr UINT_64 HINT_INT64_0X7F = INT64_MAX;
    constexpr UINT_64 HINT_INT64_0XFF = UINT64_MAX;

    constexpr HintFloat HINT_PI = 3.1415926535897932384626433832795;
    constexpr HintFloat HINT_2PI = HINT_PI * 2;
    constexpr HintFloat HINT_HSQ_ROOT2 = 0.70710678118654752440084436210485;

    constexpr UINT_64 NTT_MOD1 = 3221225473;
    constexpr UINT_64 NTT_ROOT1 = 5;
    constexpr UINT_64 NTT_MOD2 = 3489660929;
    constexpr UINT_64 NTT_ROOT2 = 3;
    constexpr size_t NTT_MAX_LEN1 = 1ull << 28;

    constexpr UINT_64 NTT_MOD3 = 79164837199873;
    constexpr UINT_64 NTT_ROOT3 = 5;
    constexpr UINT_64 NTT_MOD4 = 96757023244289;
    constexpr UINT_64 NTT_ROOT4 = 3;
    constexpr size_t NTT_MAX_LEN2 = 1ull << 43;

    HintFloat cas(HintFloat x)
    {
        return std::cos(x) + std::sin(x);
    }
    /// @brief 生成不大于n的最大的2的幂次的数
    /// @param n
    /// @return 不大于n的最大的2的幂次的数
    template <typename T>
    constexpr T max_2pow(T n)
    {
        T res = 1;
        res <<= (sizeof(T) * 8 - 1);
        while (res > n)
        {
            res /= 2;
        }
        return res;
    }
    /// @brief 生成不小于n的最小的2的幂次的数
    /// @param n
    /// @return 不小于n的最小的2的幂次的数
    template <typename T>
    constexpr T min_2pow(T n)
    {
        T res = 1;
        while (res < n)
        {
            res *= 2;
        }
        return res;
    }
    template <typename T>
    constexpr T hint_log2(T n)
    {
        T res = 0;
        while (n > 1)
        {
            n /= 2;
            res++;
        }
        return res;
    }
#if MULTITHREAD == 1
    const UINT_32 hint_threads = std::thread::hardware_concurrency();
    const UINT_32 log2_threads = std::ceil(hint_log2(hint_threads));
    std::atomic<UINT_32> cur_ths;
#endif
    template <typename T>
    constexpr bool is_neg(T x)
    {
        return x < 0;
    }
    template <typename T>
    constexpr bool is_odd(T x)
    {
        return static_cast<bool>(x & 1);
    }
    // 模板快速幂
    template <typename T>
    constexpr T qpow(T m, UINT_64 n)
    {
        T result = 1;
        while (n > 0)
        {
            if ((n & 1) != 0)
            {
                result = result * m;
            }
            m = m * m;
            n >>= 1;
        }
        return result;
    }
    // 取模快速幂
    constexpr UINT_64 qpow(UINT_64 m, UINT_64 n, UINT_64 mod)
    {
        if (m <= 1)
        {
            return m;
        }
        UINT_64 result = 1;
        while (n > 0)
        {
            if ((n & 1) != 0)
            {
                result = result * m % mod;
            }
            m = m * m % mod;
            n >>= 1;
        }
        return result;
    }
    // 模意义下的逆元
    constexpr UINT_64 mod_inv(UINT_64 n, UINT_64 mod)
    {
        return qpow(n, mod - 2, mod);
    }
    // 利用编译器优化一次性算出商和余数
    template <typename T>
    constexpr std::pair<T, T> div_mod(T a, T b)
    {
        return std::make_pair(a / b, a % b);
    }
    // 无溢出64位与64位乘,返回的pair的first为低位,second为高位
    constexpr std::pair<UINT_64, UINT_64> safe_mul128(UINT_64 a, UINT_64 b)
    {
        UINT_64 al = a & HINT_INT32_0XFF;
        UINT_64 bl = b & HINT_INT32_0XFF;
        UINT_64 ah = a >> HINT_INT_BIT;
        UINT_64 bh = b >> HINT_INT_BIT;
        UINT_64 resl = al * bl;
        UINT_64 resm = al * bh + ah * bl + (resl >> HINT_INT_BIT);
        UINT_64 resh = ah * bh + (resm >> HINT_INT_BIT);
        return std::make_pair((resm << HINT_INT_BIT) + (HINT_INT32_0XFF & resl), resh);
    }
    // 无溢出64位与32位乘
    constexpr std::pair<UINT_32, UINT_64> safe_mul96(UINT_64 a, UINT_32 b)
    {
        UINT_64 tmp1 = a & HINT_INT32_0XFF;
        UINT_64 tmp2 = a >> HINT_INT_BIT;
        tmp1 *= b;
        tmp2 *= b;
        tmp2 += (tmp1 >> HINT_INT_BIT);
        tmp1 &= HINT_INT32_0XFF;
        return std::make_pair(tmp2 >> HINT_INT_BIT, (tmp2 << HINT_INT_BIT) + tmp1);
    }
    // 无溢出64位加法
    constexpr std::pair<UINT_64, bool> safe_add(UINT_64 a, UINT_64 b)
    {
        UINT_64 tmp = HINT_INT64_0XFF - b;
        if (a > tmp)
        {
            return std::make_pair(a - tmp - 1, true);
        }
        return std::make_pair(a + b, false);
    }
    // 无溢出64位减法
    constexpr std::pair<UINT_64, bool> safe_sub(UINT_64 a, UINT_64 b)
    {
        if (a >= b)
        {
            return std::make_pair(a - b, false);
        }
        UINT_64 tmp = HINT_INT64_0XFF - b;
        return std::make_pair(a + tmp + 1, true);
    }
    // 96位整数除以64位整数
    constexpr UINT_64 div_3by2(std::pair<UINT_64, UINT_32> dividend, UINT_64 divisor)
    {
        UINT_64 rem = 0;
        UINT_64 quo = 0;
        auto tmp = div_mod(dividend.first, divisor);
        quo = tmp.first << 32;
        rem = tmp.second << 32;
        rem += dividend.second;
        auto tmp2 = div_mod(rem, divisor);
        quo += tmp2.first;
        return quo;
    }
    // 二进制末尾0的个数
    template <typename T>
    constexpr void remove_rear_zero(T &a)
    {
        if (a == 0)
        {
            return;
        }
        while ((a & 1) == 0)
        {
            a >>= 1;
        }
    }
    template <typename T>
    constexpr INT_32 count_zero(const T &a)
    {
        if (a == 0)
        {
            return CHAR_BIT * sizeof(a);
        }
        INT_32 res = 0;
        T tmp = 1;
        while ((tmp & a) == 0)
        {
            res++;
            tmp <<= 1;
        }
        return res;
    }
    // 辗转相除法最大公因数
    template <typename T>
    constexpr T gcd(const T &a, const T *b)
    {
        while (b > 0)
        {
            T tmp = std::move(b);
            b = a % b;
            a = std::move(tmp);
        }
        return a;
    }
    // 辗转相除法最大公因数
    template <typename T>
    constexpr T gcd_stein(T a, T b)
    {
        if (a == 0 || b == 0)
        {
            return 0;
        }
        const INT_32 a_zero = count_zero(a);
        const INT_32 b_zero = count_zero(b);
        a >>= a_zero;
        b >>= b_zero;
        if (a < b)
        {
            swap(a, b);
        }
        while (a > 0)
        {
            remove_rear_zero(a);
            if (a < b)
            {
                swap(a, b);
            }
            a -= b;
        }
        return b << std::min(a_zero, b_zero);
    }
    // 中国剩余定理
    UINT_64 crt(UINT_64 mods[], UINT_64 nums[], size_t n)
    {
        UINT_64 result = 0, mod_product = 1;
        for (size_t i = 0; i < n; i++)
        {
            mod_product *= mods[i];
        }
        for (size_t i = 0; i < n; i++)
        {
            UINT_64 mod = mods[i];
            UINT_64 tmp = mod_product / mod;
            UINT_64 inv = mod_inv(tmp, mod);
            result += nums[i] * tmp * inv % mod_product;
        }
        return result % mod_product;
    }

    /// @brief 快速计算两模数的中国剩余定理，返回n
    /// @param num1 n模除mod1的余数
    /// @param num2 n模除mod2的余数
    /// @param mod1 第一个模数
    /// @param mod2 第二个模数
    /// @return n的最小解
    template <UINT_64 MOD1, UINT_64 MOD2>
    constexpr UINT_64 qcrt(UINT_64 num1, UINT_64 num2)
    {
        constexpr UINT_64 inv1 = mod_inv(MOD1, MOD2);
        constexpr UINT_64 inv2 = mod_inv(MOD2, MOD1);
        if (num1 > num2)
        {
            return ((num1 - num2) * inv2 % MOD1) * MOD2 + num2;
        }
        else
        {
            return ((num2 - num1) * inv1 % MOD2) * MOD1 + num1;
        }
    }
    // 模板数组拷贝
    template <typename T>
    void ary_copy(T *target, const T *source, size_t len)
    {
        if (len == 0 || target == source)
        {
            return;
        }
        if (len >= INT64_MAX)
        {
            throw("Ary too long\n");
        }
        // std::memcpy(target, source, len * sizeof(T));
        std::copy(source, source + len, target);
    }
    // 模板数组拷贝
    template <typename T1, typename T2>
    void ary_copy_2type(T1 *target, const T2 *source, size_t len)
    {
        for (size_t i = 0; i < len; i++)
        {
            target[i] = static_cast<T1>(source[i]);
        }
    }
    // 去除数组前导零后的长度
    template <typename T>
    constexpr size_t ary_true_len(const T &ary, size_t len)
    {
        while (len > 0 && ary[len - 1] == 0)
        {
            len--;
        }
        return len;
    }
    // 模版数组清零
    template <typename T>
    inline void ary_clr(T *ptr, size_t len)
    {
        memset(ptr, 0, len * sizeof(T));
    }
    // 重分配空间
    template <typename T>
    inline T *ary_realloc(T *ptr, size_t len)
    {
        if (len * sizeof(T) < INT64_MAX)
        {
            ptr = static_cast<T *>(realloc(ptr, len * sizeof(T)));
        }
        if (ptr == nullptr)
        {
            throw("realloc error");
        }
        return ptr;
    }
    // 从其他类型数组拷贝到复数组实部
    template <typename T>
    inline void com_ary_real_copy(Complex *target, const T &source, size_t len)
    {
        for (size_t i = 0; i < len; i++)
        {
            target[i] = Complex(source[i], target[i].imag());
        }
    }
    // 从其他类型数组拷贝到复数组虚部
    template <typename T>
    inline void com_ary_img_copy(Complex *target, const T &source, size_t len)
    {
        for (size_t i = 0; i < len; i++)
        {
            target[i] = Complex(target[i].real(), source[i]);
        }
    }
    // 从其他类型数组拷贝到复数组
    template <typename T>
    inline void com_ary_combine_copy(Complex *target, const T &source1, size_t len1, const T &source2, size_t len2)
    {
        size_t min_len = std::min(len1, len2);
        size_t i = 0;
        while (i < min_len)
        {
            target[i] = Complex(source1[i], source2[i]);
            i++;
        }
        while (i < len1)
        {
            target[i].real(source1[i]);
            i++;
        }
        while (i < len2)
        {
            target[i].imag(source2[i]);
            i++;
        }
    }
    // 数组按位相乘
    template <typename T>
    inline void ary_mul(const T in1[], const T in2[], T out[], size_t len)
    {
        size_t mod4 = len % 4;
        len -= mod4;
        for (size_t i = 0; i < len; i += 4)
        {
            out[i] = in1[i] * in2[i];
            out[i + 1] = in1[i + 1] * in2[i + 1];
            out[i + 2] = in1[i + 2] * in2[i + 2];
            out[i + 3] = in1[i + 3] * in2[i + 3];
        }
        for (size_t i = len; i < len + mod4; i++)
        {
            out[i] = in1[i] * in2[i];
        }
    }
    // 数组交错重排
    template <UINT_64 N, typename T>
    void ary_interlace(T ary[], size_t len)
    {
        size_t sub_len = len / N;
        T *tmp_ary = new T[len - sub_len];
        for (size_t i = 0; i < len; i += N)
        {
            ary[i / N] = ary[i];
            for (size_t j = 0; j < N - 1; j++)
            {
                tmp_ary[j * sub_len + i / N] = ary[i + j + 1];
            }
        }
        ary_copy(ary + sub_len, tmp_ary, len - sub_len);
        delete[] tmp_ary;
    }
    // 数组分块
    template <size_t CHUNK, typename T1, typename T2>
    void ary_chunk_split(T1 input[], T2 output[], size_t in_len)
    {
        // 将输入数组视为一整块连续的数据,从第一个比特开始,每CHUNK个bit为一组，依次放到输出结果数组中
        if (sizeof(T1) < CHUNK)
        {
            return;
        }
        constexpr T1 MAX = (1 << (CHUNK - 1)) - 1 + (1 << (CHUNK - 1)); // 二进制CHUNK bit全为1的数

        T1 mask = MAX;
    }
    // 分块合并
    template <size_t CHUNK, typename T1, typename T2>
    void ary_chunk_merge(T1 input[], T2 output[], size_t in_len)
    {
        // 将输入数组的元素视为一个个CHUNK bit的数据,从第一个比特开始,依次连续放到输出结果数组中
    }
    // FFT与类FFT变换的命名空间
    namespace hint_transform
    {
        // 二进制逆序
        template <typename T>
        void binary_reverse_swap(T &ary, size_t len)
        {
            size_t i = 0;
            for (size_t j = 1; j < len - 1; j++)
            {
                size_t k = len >> 1;
                i ^= k;
                while (k > i)
                {
                    k >>= 1;
                    i ^= k;
                };
                if (j < i)
                {
                    std::swap(ary[i], ary[j]);
                }
            }
        }
        // 四进制逆序
        template <typename SizeType = UINT_32, typename T>
        void quaternary_reverse_swap(T &ary, size_t len)
        {
            SizeType log_n = hint_log2(len);
            SizeType *rev = new SizeType[len / 4];
            rev[0] = 0;
            for (SizeType i = 1; i < len; i++)
            {
                SizeType index = (rev[i >> 2] >> 2) | ((i & 3) << (log_n - 2)); // 求rev交换数组
                if (i < len / 4)
                {
                    rev[i] = index;
                }
                if (i < index)
                {
                    std::swap(ary[i], ary[index]);
                }
            }
            delete[] rev;
        }
        namespace hint_fft
        {
            // 返回单位圆上辐角为theta的点
            static Complex unit_root(HintFloat theta)
            {
                return std::polar<HintFloat>(1.0, theta);
            }
            // 返回单位圆上平分m份的第n个
            static Complex unit_root(size_t m, size_t n)
            {
                return unit_root((HINT_2PI * n) / m);
            }
            class ComplexTable
            {
            private:
                std::vector<Complex> table;
                INT_32 max_log_size = 2;
                INT_32 cur_log_size = 2;

                ComplexTable(const ComplexTable &) = delete;
                ComplexTable &operator=(const ComplexTable &) = delete;

            public:
                ~ComplexTable() {}
                // 初始化可以生成平分圆1<<shift份产生的单位根的表
                ComplexTable(UINT_32 max_shift)
                {
                    max_shift = std::max<size_t>(max_shift, 2);
                    max_log_size = max_shift;
                    size_t ary_size = 1ull << (max_shift - 1);
                    table.resize(ary_size);
                    table[0] = Complex(1);
#if TABLE_PRELOAD == 1
                    expand(max_shift);
#endif
                }
                void expand(INT_32 shift)
                {
                    if (shift > max_log_size)
                    {
                        throw("FFT length too long for lut\n");
                    }
                    for (INT_32 i = cur_log_size + 1; i <= shift; i++)
                    {
                        size_t len = 1ull << i, vec_size = len / 4;
                        table[vec_size] = Complex(1, 0);
                        for (size_t pos = 0; pos < vec_size / 2; pos++)
                        {
                            table[vec_size + pos * 2] = table[vec_size / 2 + pos];
                            if (pos % 2 == 1)
                            {
                                Complex tmp = unit_root(len, pos);
                                table[vec_size + pos] = tmp;
                                table[vec_size * 2 - pos] = Complex(tmp.imag(), tmp.real());
                            }
                        }
                        table[vec_size + vec_size / 2] = unit_root(8, 1);
                    }
                    cur_log_size = std::max(cur_log_size, shift);
                }
                // shift表示圆平分为1<<shift份,n表示第几个单位根
                Complex get_omega(UINT_32 shift, size_t n) const
                {
                    size_t rank = 1ull << shift;
                    const size_t rank_ff = rank - 1, quad_n = n << 2;
                    // n &= rank_ff;
                    size_t zone = quad_n >> shift; // 第几象限
                    if ((quad_n & rank_ff) == 0)
                    {
                        static constexpr Complex ONES_CONJ[4] = {Complex(1, 0), Complex(0, -1), Complex(-1, 0), Complex(0, 1)};
                        return ONES_CONJ[zone];
                    }
                    Complex tmp;
                    if ((zone & 2) == 0)
                    {
                        if ((zone & 1) == 0)
                        {
                            tmp = table[rank / 4 + n];
                            tmp.imag(-tmp.imag());
                        }
                        else
                        {
                            tmp = -table[rank - rank / 4 - n];
                        }
                    }
                    else
                    {
                        if ((zone & 1) == 0)
                        {
                            tmp = table[n - (rank / 4)];
                            tmp.real(-tmp.real());
                        }
                        else
                        {
                            tmp = table[rank + rank / 4 - n];
                        }
                    }
                    return tmp;
                }
            };

            class ComplexTableX
            {
            private:
                std::vector<std::vector<Complex>> table;
                INT_32 max_log_size = 2;
                INT_32 cur_log_size = 2;

                ComplexTableX(const ComplexTableX &) = delete;
                ComplexTableX &operator=(const ComplexTableX &) = delete;

            public:
                ~ComplexTableX() {}
                // 初始化可以生成平分圆1<<shift份产生的单位根的表
                ComplexTableX(UINT_32 max_shift)
                {
                    max_shift = std::max<size_t>(max_shift, cur_log_size);
                    max_log_size = max_shift;
                    table.resize(max_shift + 1);
                    table[0] = table[1] = std::vector<Complex>{1};
                    table[2] = std::vector<Complex>{Complex(1, 0), Complex(0, -1), Complex(-1, 0)};
#if TABLE_PRELOAD == 1
                    expand(max_shift);
#endif
                }
                void expand(INT_32 shift)
                {
                    if (shift > max_log_size)
                    {
                        throw("FFT length too long for lut\n");
                    }
                    for (INT_32 i = cur_log_size + 1; i <= shift; i++)
                    {
                        size_t len = 1ull << i, vec_size = len * 3 / 4;
                        table[i].resize(vec_size);
                        for (size_t pos = 0; pos < len / 8; pos++)
                        {
                            table[i][pos * 2] = table[i - 1][pos];
                            table[i][pos * 2 + len / 4] = table[i - 1][pos + len / 8];
                            table[i][pos * 2 + len / 2] = table[i - 1][pos + len / 4];
                            if (pos % 2 == 1)
                            {
                                HintFloat cos_theta = std::cos(HINT_2PI * pos / len);
                                HintFloat sin_theta = std::sin(HINT_2PI * pos / len);
                                Complex tmp1(cos_theta, -sin_theta);
                                Complex tmp2(sin_theta, -cos_theta);

                                table[i][pos] = tmp1;
                                table[i][pos + len / 4] = Complex(tmp1.imag(), -tmp1.real());
                                table[i][pos + len / 2] = -tmp1;

                                table[i][len / 4 - pos] = tmp2;
                                table[i][len / 2 - pos] = Complex(tmp2.imag(), -tmp2.real());
                                table[i][vec_size - pos] = -tmp2;
                            }
                        }
                        table[i][len / 8] = std::conj(unit_root(8, 1));
                        table[i][len * 3 / 8] = std::conj(unit_root(8, 3));
                        table[i][len * 5 / 8] = std::conj(unit_root(8, 5));
                    }
                    cur_log_size = std::max(cur_log_size, shift);
                }
                // shift表示圆平分为1<<shift份,n表示第几个单位根
                Complex get_omega(UINT_32 shift, size_t n) const
                {
                    return table[shift][n];
                }
            };

            constexpr size_t lut_max_rank = 23;
#if TABLE_TYPE == 0
            static ComplexTable TABLE(lut_max_rank);
#elif TABLE_TYPE == 1
            static ComplexTableX TABLE(lut_max_rank);
#else
#error TABLE_TYPE must be 0,1
#endif
            // 2点fft
            template <typename T>
            inline void fft_2point(T &sum, T &diff)
            {
                T tmp0 = sum;
                T tmp1 = diff;
                sum = tmp0 + tmp1;
                diff = tmp0 - tmp1;
            }
            // 4点fft
            inline void fft_4point(Complex *input, size_t rank = 1)
            {
                Complex tmp0 = input[0];
                Complex tmp1 = input[rank];
                Complex tmp2 = input[rank * 2];
                Complex tmp3 = input[rank * 3];

                fft_2point(tmp0, tmp2);
                fft_2point(tmp1, tmp3);
                tmp3 = Complex(tmp3.imag(), -tmp3.real());

                input[0] = tmp0 + tmp1;
                input[rank] = tmp2 + tmp3;
                input[rank * 2] = tmp0 - tmp1;
                input[rank * 3] = tmp2 - tmp3;
            }
            inline void fft_dit_4point(Complex *input, size_t rank = 1)
            {
                Complex tmp0 = input[0];
                Complex tmp1 = input[rank];
                Complex tmp2 = input[rank * 2];
                Complex tmp3 = input[rank * 3];

                fft_2point(tmp0, tmp1);
                fft_2point(tmp2, tmp3);
                tmp3 = Complex(tmp3.imag(), -tmp3.real());

                input[0] = tmp0 + tmp2;
                input[rank] = tmp1 + tmp3;
                input[rank * 2] = tmp0 - tmp2;
                input[rank * 3] = tmp1 - tmp3;
            }
            inline void fft_dit_8point(Complex *input, size_t rank = 1)
            {
                Complex tmp0 = input[0];
                Complex tmp1 = input[rank];
                Complex tmp2 = input[rank * 2];
                Complex tmp3 = input[rank * 3];
                Complex tmp4 = input[rank * 4];
                Complex tmp5 = input[rank * 5];
                Complex tmp6 = input[rank * 6];
                Complex tmp7 = input[rank * 7];
                fft_2point(tmp0, tmp1);
                fft_2point(tmp2, tmp3);
                fft_2point(tmp4, tmp5);
                fft_2point(tmp6, tmp7);
                tmp3 = Complex(tmp3.imag(), -tmp3.real());
                tmp7 = Complex(tmp7.imag(), -tmp7.real());

                fft_2point(tmp0, tmp2);
                fft_2point(tmp1, tmp3);
                fft_2point(tmp4, tmp6);
                fft_2point(tmp5, tmp7);
                static constexpr HintFloat cos_1_8 = 0.70710678118654752440084436210485;
                tmp5 = cos_1_8 * Complex(tmp5.imag() + tmp5.real(), tmp5.imag() - tmp5.real());
                tmp6 = Complex(tmp6.imag(), -tmp6.real());
                tmp7 = -cos_1_8 * Complex(tmp7.real() - tmp7.imag(), tmp7.real() + tmp7.imag());

                input[0] = tmp0 + tmp4;
                input[rank] = tmp1 + tmp5;
                input[rank * 2] = tmp2 + tmp6;
                input[rank * 3] = tmp3 + tmp7;
                input[rank * 4] = tmp0 - tmp4;
                input[rank * 5] = tmp1 - tmp5;
                input[rank * 6] = tmp2 - tmp6;
                input[rank * 7] = tmp3 - tmp7;
            }
            inline void fft_dit_16point(Complex *input, size_t rank = 1)
            {
                static constexpr HintFloat cos_1_8 = 0.70710678118654752440084436210485;
                static constexpr HintFloat cos_1_16 = 0.92387953251128675612818318939679;
                static constexpr HintFloat sin_1_16 = 0.3826834323650897717284599840304;
                static constexpr Complex w1(cos_1_16, -sin_1_16), w3(sin_1_16, -cos_1_16);
                static constexpr Complex w5(-sin_1_16, -cos_1_16), w7(-cos_1_16, -sin_1_16);

                fft_dit_8point(input, rank);
                fft_dit_8point(input + rank * 8, rank);

                Complex tmp0 = input[0];
                Complex tmp1 = input[rank];
                Complex tmp2 = input[rank * 8];
                Complex tmp3 = input[rank * 9] * w1;
                input[0] = tmp0 + tmp2;
                input[rank] = tmp1 + tmp3;
                input[rank * 8] = tmp0 - tmp2;
                input[rank * 9] = tmp1 - tmp3;

                tmp0 = input[rank * 2];
                tmp1 = input[rank * 3];
                tmp2 = input[rank * 10];
                tmp3 = input[rank * 11] * w3;
                tmp2 = cos_1_8 * Complex(tmp2.imag() + tmp2.real(), tmp2.imag() - tmp2.real());
                input[rank * 2] = tmp0 + tmp2;
                input[rank * 3] = tmp1 + tmp3;
                input[rank * 10] = tmp0 - tmp2;
                input[rank * 11] = tmp1 - tmp3;

                tmp0 = input[rank * 4];
                tmp1 = input[rank * 5];
                tmp2 = input[rank * 12];
                tmp3 = input[rank * 13] * w5;
                tmp2 = Complex(tmp2.imag(), -tmp2.real());
                input[rank * 4] = tmp0 + tmp2;
                input[rank * 5] = tmp1 + tmp3;
                input[rank * 12] = tmp0 - tmp2;
                input[rank * 13] = tmp1 - tmp3;

                tmp0 = input[rank * 6];
                tmp1 = input[rank * 7];
                tmp2 = input[rank * 14];
                tmp3 = input[rank * 15] * w7;
                tmp2 = -cos_1_8 * Complex(tmp2.real() - tmp2.imag(), tmp2.real() + tmp2.imag());
                input[rank * 6] = tmp0 + tmp2;
                input[rank * 7] = tmp1 + tmp3;
                input[rank * 14] = tmp0 - tmp2;
                input[rank * 15] = tmp1 - tmp3;
            }
            inline void fft_dit_32point(Complex *input, size_t rank = 1)
            {
                static constexpr HintFloat cos_1_8 = 0.70710678118654752440084436210485;
                static constexpr HintFloat cos_1_16 = 0.92387953251128675612818318939679;
                static constexpr HintFloat sin_1_16 = 0.3826834323650897717284599840304;
                static constexpr HintFloat cos_1_32 = 0.98078528040323044912618223613424;
                static constexpr HintFloat sin_1_32 = 0.19509032201612826784828486847702;
                static constexpr HintFloat cos_3_32 = 0.83146961230254523707878837761791;
                static constexpr HintFloat sin_3_32 = 0.55557023301960222474283081394853;
                static constexpr Complex w1(cos_1_32, -sin_1_32), w2(cos_1_16, -sin_1_16), w3(cos_3_32, -sin_3_32);
                static constexpr Complex w5(sin_3_32, -cos_3_32), w6(sin_1_16, -cos_1_16), w7(sin_1_32, -cos_1_32);
                static constexpr Complex w9(-sin_1_32, -cos_1_32), w10(-sin_1_16, -cos_1_16), w11(-sin_3_32, -cos_3_32);
                static constexpr Complex w13(-cos_3_32, -sin_3_32), w14(-cos_1_16, -sin_1_16), w15(-cos_1_32, -sin_1_32);

                fft_dit_16point(input, rank);
                fft_dit_16point(input + rank * 16, rank);

                Complex tmp0 = input[0];
                Complex tmp1 = input[rank];
                Complex tmp2 = input[rank * 16];
                Complex tmp3 = input[rank * 17] * w1;
                input[0] = tmp0 + tmp2;
                input[rank] = tmp1 + tmp3;
                input[rank * 16] = tmp0 - tmp2;
                input[rank * 17] = tmp1 - tmp3;

                tmp0 = input[rank * 2];
                tmp1 = input[rank * 3];
                tmp2 = input[rank * 18] * w2;
                tmp3 = input[rank * 19] * w3;
                input[rank * 2] = tmp0 + tmp2;
                input[rank * 3] = tmp1 + tmp3;
                input[rank * 18] = tmp0 - tmp2;
                input[rank * 19] = tmp1 - tmp3;

                tmp0 = input[rank * 4];
                tmp1 = input[rank * 5];
                tmp2 = input[rank * 20];
                tmp3 = input[rank * 21] * w5;
                tmp2 = cos_1_8 * Complex(tmp2.imag() + tmp2.real(), tmp2.imag() - tmp2.real());
                input[rank * 4] = tmp0 + tmp2;
                input[rank * 5] = tmp1 + tmp3;
                input[rank * 20] = tmp0 - tmp2;
                input[rank * 21] = tmp1 - tmp3;

                tmp0 = input[rank * 6];
                tmp1 = input[rank * 7];
                tmp2 = input[rank * 22] * w6;
                tmp3 = input[rank * 23] * w7;
                input[rank * 6] = tmp0 + tmp2;
                input[rank * 7] = tmp1 + tmp3;
                input[rank * 22] = tmp0 - tmp2;
                input[rank * 23] = tmp1 - tmp3;

                tmp0 = input[rank * 8];
                tmp1 = input[rank * 9];
                tmp2 = input[rank * 24];
                tmp3 = input[rank * 25] * w9;
                tmp2 = Complex(tmp2.imag(), -tmp2.real());
                input[rank * 8] = tmp0 + tmp2;
                input[rank * 9] = tmp1 + tmp3;
                input[rank * 24] = tmp0 - tmp2;
                input[rank * 25] = tmp1 - tmp3;

                tmp0 = input[rank * 10];
                tmp1 = input[rank * 11];
                tmp2 = input[rank * 26] * w10;
                tmp3 = input[rank * 27] * w11;
                input[rank * 10] = tmp0 + tmp2;
                input[rank * 11] = tmp1 + tmp3;
                input[rank * 26] = tmp0 - tmp2;
                input[rank * 27] = tmp1 - tmp3;

                tmp0 = input[rank * 12];
                tmp1 = input[rank * 13];
                tmp2 = input[rank * 28];
                tmp3 = input[rank * 29] * w13;
                tmp2 = -cos_1_8 * Complex(tmp2.real() - tmp2.imag(), tmp2.real() + tmp2.imag());
                input[rank * 12] = tmp0 + tmp2;
                input[rank * 13] = tmp1 + tmp3;
                input[rank * 28] = tmp0 - tmp2;
                input[rank * 29] = tmp1 - tmp3;

                tmp0 = input[rank * 14];
                tmp1 = input[rank * 15];
                tmp2 = input[rank * 30] * w14;
                tmp3 = input[rank * 31] * w15;

                input[rank * 14] = tmp0 + tmp2;
                input[rank * 15] = tmp1 + tmp3;
                input[rank * 30] = tmp0 - tmp2;
                input[rank * 31] = tmp1 - tmp3;
            }
            inline void fft_dif_4point(Complex *input, size_t rank = 1)
            {
                Complex tmp0 = input[0];
                Complex tmp1 = input[rank];
                Complex tmp2 = input[rank * 2];
                Complex tmp3 = input[rank * 3];

                fft_2point(tmp0, tmp2);
                fft_2point(tmp1, tmp3);
                tmp3 = Complex(tmp3.imag(), -tmp3.real());

                input[0] = tmp0 + tmp1;
                input[rank] = tmp0 - tmp1;
                input[rank * 2] = tmp2 + tmp3;
                input[rank * 3] = tmp2 - tmp3;
            }
            inline void fft_dif_8point(Complex *input, size_t rank = 1)
            {
                Complex tmp0 = input[0];
                Complex tmp1 = input[rank];
                Complex tmp2 = input[rank * 2];
                Complex tmp3 = input[rank * 3];
                Complex tmp4 = input[rank * 4];
                Complex tmp5 = input[rank * 5];
                Complex tmp6 = input[rank * 6];
                Complex tmp7 = input[rank * 7];

                fft_2point(tmp0, tmp4);
                fft_2point(tmp1, tmp5);
                fft_2point(tmp2, tmp6);
                fft_2point(tmp3, tmp7);
                static constexpr HintFloat cos_1_8 = 0.70710678118654752440084436210485;
                tmp5 = cos_1_8 * Complex(tmp5.imag() + tmp5.real(), tmp5.imag() - tmp5.real());
                tmp6 = Complex(tmp6.imag(), -tmp6.real());
                tmp7 = -cos_1_8 * Complex(tmp7.real() - tmp7.imag(), tmp7.real() + tmp7.imag());

                fft_2point(tmp0, tmp2);
                fft_2point(tmp1, tmp3);
                fft_2point(tmp4, tmp6);
                fft_2point(tmp5, tmp7);
                tmp3 = Complex(tmp3.imag(), -tmp3.real());
                tmp7 = Complex(tmp7.imag(), -tmp7.real());

                input[0] = tmp0 + tmp1;
                input[rank] = tmp0 - tmp1;
                input[rank * 2] = tmp2 + tmp3;
                input[rank * 3] = tmp2 - tmp3;
                input[rank * 4] = tmp4 + tmp5;
                input[rank * 5] = tmp4 - tmp5;
                input[rank * 6] = tmp6 + tmp7;
                input[rank * 7] = tmp6 - tmp7;
            }
            inline void fft_dif_16point(Complex *input, size_t rank = 1)
            {
                static constexpr HintFloat cos_1_8 = 0.70710678118654752440084436210485;
                static constexpr HintFloat cos_1_16 = 0.92387953251128675612818318939679;
                static constexpr HintFloat sin_1_16 = 0.3826834323650897717284599840304;
                static constexpr Complex w1(cos_1_16, -sin_1_16), w3(sin_1_16, -cos_1_16);
                static constexpr Complex w5(-sin_1_16, -cos_1_16), w7(-cos_1_16, -sin_1_16);

                Complex tmp0 = input[0];
                Complex tmp1 = input[rank];
                Complex tmp2 = input[rank * 8];
                Complex tmp3 = input[rank * 9];
                input[0] = tmp0 + tmp2;
                input[rank] = tmp1 + tmp3;
                input[rank * 8] = tmp0 - tmp2;
                input[rank * 9] = (tmp1 - tmp3) * w1;

                tmp0 = input[rank * 2];
                tmp1 = input[rank * 3];
                tmp2 = input[rank * 10];
                tmp3 = input[rank * 11];
                fft_2point(tmp0, tmp2);
                tmp2 = cos_1_8 * Complex(tmp2.imag() + tmp2.real(), tmp2.imag() - tmp2.real());
                input[rank * 2] = tmp0;
                input[rank * 3] = tmp1 + tmp3;
                input[rank * 10] = tmp2;
                input[rank * 11] = (tmp1 - tmp3) * w3;

                tmp0 = input[rank * 4];
                tmp1 = input[rank * 5];
                tmp2 = input[rank * 12];
                tmp3 = input[rank * 13];
                fft_2point(tmp0, tmp2);
                tmp2 = Complex(tmp2.imag(), -tmp2.real());
                input[rank * 4] = tmp0;
                input[rank * 5] = tmp1 + tmp3;
                input[rank * 12] = tmp2;
                input[rank * 13] = (tmp1 - tmp3) * w5;

                tmp0 = input[rank * 6];
                tmp1 = input[rank * 7];
                tmp2 = input[rank * 14];
                tmp3 = input[rank * 15];
                fft_2point(tmp0, tmp2);
                tmp2 = -cos_1_8 * Complex(tmp2.real() - tmp2.imag(), tmp2.real() + tmp2.imag());
                input[rank * 6] = tmp0;
                input[rank * 7] = tmp1 + tmp3;
                input[rank * 14] = tmp2;
                input[rank * 15] = (tmp1 - tmp3) * w7;

                fft_dif_8point(input, rank);
                fft_dif_8point(input + rank * 8, rank);
            }
            inline void fft_dif_32point(Complex *input, size_t rank = 1)
            {
                static constexpr HintFloat cos_1_8 = 0.70710678118654752440084436210485;
                static constexpr HintFloat cos_1_16 = 0.92387953251128675612818318939679;
                static constexpr HintFloat sin_1_16 = 0.3826834323650897717284599840304;
                static constexpr HintFloat cos_1_32 = 0.98078528040323044912618223613424;
                static constexpr HintFloat sin_1_32 = 0.19509032201612826784828486847702;
                static constexpr HintFloat cos_3_32 = 0.83146961230254523707878837761791;
                static constexpr HintFloat sin_3_32 = 0.55557023301960222474283081394853;
                static constexpr Complex w1(cos_1_32, -sin_1_32), w2(cos_1_16, -sin_1_16), w3(cos_3_32, -sin_3_32);
                static constexpr Complex w5(sin_3_32, -cos_3_32), w6(sin_1_16, -cos_1_16), w7(sin_1_32, -cos_1_32);
                static constexpr Complex w9(-sin_1_32, -cos_1_32), w10(-sin_1_16, -cos_1_16), w11(-sin_3_32, -cos_3_32);
                static constexpr Complex w13(-cos_3_32, -sin_3_32), w14(-cos_1_16, -sin_1_16), w15(-cos_1_32, -sin_1_32);

                Complex tmp0 = input[0];
                Complex tmp1 = input[rank];
                Complex tmp2 = input[rank * 16];
                Complex tmp3 = input[rank * 17];
                input[0] = tmp0 + tmp2;
                input[rank] = tmp1 + tmp3;
                input[rank * 16] = tmp0 - tmp2;
                input[rank * 17] = (tmp1 - tmp3) * w1;

                tmp0 = input[rank * 2];
                tmp1 = input[rank * 3];
                tmp2 = input[rank * 18];
                tmp3 = input[rank * 19];
                input[rank * 2] = tmp0 + tmp2;
                input[rank * 3] = tmp1 + tmp3;
                input[rank * 18] = (tmp0 - tmp2) * w2;
                input[rank * 19] = (tmp1 - tmp3) * w3;

                tmp0 = input[rank * 4];
                tmp1 = input[rank * 5];
                tmp2 = input[rank * 20];
                tmp3 = input[rank * 21];
                fft_2point(tmp0, tmp2);
                tmp2 = cos_1_8 * Complex(tmp2.imag() + tmp2.real(), tmp2.imag() - tmp2.real());
                input[rank * 4] = tmp0;
                input[rank * 5] = tmp1 + tmp3;
                input[rank * 20] = tmp2;
                input[rank * 21] = (tmp1 - tmp3) * w5;

                tmp0 = input[rank * 6];
                tmp1 = input[rank * 7];
                tmp2 = input[rank * 22];
                tmp3 = input[rank * 23];
                input[rank * 6] = tmp0 + tmp2;
                input[rank * 7] = tmp1 + tmp3;
                input[rank * 22] = (tmp0 - tmp2) * w6;
                input[rank * 23] = (tmp1 - tmp3) * w7;

                tmp0 = input[rank * 8];
                tmp1 = input[rank * 9];
                tmp2 = input[rank * 24];
                tmp3 = input[rank * 25];
                fft_2point(tmp0, tmp2);
                tmp2 = Complex(tmp2.imag(), -tmp2.real());
                input[rank * 8] = tmp0;
                input[rank * 9] = tmp1 + tmp3;
                input[rank * 24] = tmp2;
                input[rank * 25] = (tmp1 - tmp3) * w9;

                tmp0 = input[rank * 10];
                tmp1 = input[rank * 11];
                tmp2 = input[rank * 26];
                tmp3 = input[rank * 27];
                input[rank * 10] = tmp0 + tmp2;
                input[rank * 11] = tmp1 + tmp3;
                input[rank * 26] = (tmp0 - tmp2) * w10;
                input[rank * 27] = (tmp1 - tmp3) * w11;

                tmp0 = input[rank * 12];
                tmp1 = input[rank * 13];
                tmp2 = input[rank * 28];
                tmp3 = input[rank * 29];
                fft_2point(tmp0, tmp2);
                tmp2 = -cos_1_8 * Complex(tmp2.real() - tmp2.imag(), tmp2.real() + tmp2.imag());
                input[rank * 12] = tmp0;
                input[rank * 13] = tmp1 + tmp3;
                input[rank * 28] = tmp2;
                input[rank * 29] = (tmp1 - tmp3) * w13;

                tmp0 = input[rank * 14];
                tmp1 = input[rank * 15];
                tmp2 = input[rank * 30];
                tmp3 = input[rank * 31];

                input[rank * 14] = tmp0 + tmp2;
                input[rank * 15] = tmp1 + tmp3;
                input[rank * 30] = (tmp0 - tmp2) * w14;
                input[rank * 31] = (tmp1 - tmp3) * w15;

                fft_dif_16point(input, rank);
                fft_dif_16point(input + rank * 16, rank);
            }

            // fft基2时间抽取蝶形变换
            inline void fft_radix2_dit_butterfly(Complex omega, Complex *input, size_t rank)
            {
                Complex tmp0 = input[0];
                Complex tmp1 = input[rank] * omega;
                input[0] = tmp0 + tmp1;
                input[rank] = tmp0 - tmp1;
            }
            // fft基2频率抽取蝶形变换
            inline void fft_radix2_dif_butterfly(Complex omega, Complex *input, size_t rank)
            {
                Complex tmp0 = input[0];
                Complex tmp1 = input[rank];
                input[0] = tmp0 + tmp1;
                input[rank] = (tmp0 - tmp1) * omega;
            }

            // fft分裂基时间抽取蝶形变换
            inline void fft_split_radix_dit_butterfly(Complex omega, Complex omega_cube,
                                                      Complex *input, size_t rank)
            {
                Complex tmp0 = input[0];
                Complex tmp1 = input[rank];
                Complex tmp2 = input[rank * 2] * omega;
                Complex tmp3 = input[rank * 3] * omega_cube;

                fft_2point(tmp2, tmp3);
                tmp3 = Complex(tmp3.imag(), -tmp3.real());

                input[0] = tmp0 + tmp2;
                input[rank] = tmp1 + tmp3;
                input[rank * 2] = tmp0 - tmp2;
                input[rank * 3] = tmp1 - tmp3;
            }
            // fft分裂基频率抽取蝶形变换
            inline void fft_split_radix_dif_butterfly(Complex omega, Complex omega_cube,
                                                      Complex *input, size_t rank)
            {
                Complex tmp0 = input[0];
                Complex tmp1 = input[rank];
                Complex tmp2 = input[rank * 2];
                Complex tmp3 = input[rank * 3];

                fft_2point(tmp0, tmp2);
                fft_2point(tmp1, tmp3);
                tmp3 = Complex(tmp3.imag(), -tmp3.real());

                input[0] = tmp0;
                input[rank] = tmp1;
                input[rank * 2] = (tmp2 + tmp3) * omega;
                input[rank * 3] = (tmp2 - tmp3) * omega_cube;
            }
            // fft基4时间抽取蝶形变换
            inline void fft_radix4_dit_butterfly(Complex omega, Complex omega_sqr, Complex omega_cube,
                                                 Complex *input, size_t rank)
            {
                Complex tmp0 = input[0];
                Complex tmp1 = input[rank] * omega;
                Complex tmp2 = input[rank * 2] * omega_sqr;
                Complex tmp3 = input[rank * 3] * omega_cube;

                fft_2point(tmp0, tmp2);
                fft_2point(tmp1, tmp3);
                tmp3 = Complex(tmp3.imag(), -tmp3.real());

                input[0] = tmp0 + tmp1;
                input[rank] = tmp2 + tmp3;
                input[rank * 2] = tmp0 - tmp1;
                input[rank * 3] = tmp2 - tmp3;
            }
            // fft基4频率抽取蝶形变换
            inline void fft_radix4_dif_butterfly(Complex omega, Complex omega_sqr, Complex omega_cube,
                                                 Complex *input, size_t rank)
            {
                Complex tmp0 = input[0];
                Complex tmp1 = input[rank];
                Complex tmp2 = input[rank * 2];
                Complex tmp3 = input[rank * 3];

                fft_2point(tmp0, tmp2);
                fft_2point(tmp1, tmp3);
                tmp3 = Complex(tmp3.imag(), -tmp3.real());

                input[0] = tmp0 + tmp1;
                input[rank] = (tmp2 + tmp3) * omega;
                input[rank * 2] = (tmp0 - tmp1) * omega_sqr;
                input[rank * 3] = (tmp2 - tmp3) * omega_cube;
            }
            // 求共轭复数及归一化，逆变换用
            inline void fft_conj(Complex *input, size_t fft_len, HintFloat div = 1)
            {
                for (size_t i = 0; i < fft_len; i++)
                {
                    input[i] = std::conj(input[i]) / div;
                }
            }
            // 归一化,逆变换用
            inline void fft_normalize(Complex *input, size_t fft_len)
            {
                HintFloat len = static_cast<HintFloat>(fft_len);
                for (size_t i = 0; i < fft_len; i++)
                {
                    input[i] /= len;
                }
            }
            // 经典模板,学习用
            void fft_radix2_dit(Complex *input, size_t fft_len)
            {
                fft_len = max_2pow(fft_len);
                binary_reverse_swap(input, fft_len);
                for (size_t rank = 1; rank < fft_len; rank *= 2)
                {
                    // rank表示上一级fft的长度,gap表示由两个上一级可以迭代计算出这一级的长度
                    size_t gap = rank * 2;
                    Complex unit_omega = std::polar<HintFloat>(1, -HINT_2PI / gap);
                    for (size_t begin = 0; begin < fft_len; begin += gap)
                    {
                        Complex omega = Complex(1, 0);
                        for (size_t pos = begin; pos < begin + rank; pos++)
                        {
                            fft_radix2_dit_butterfly(omega, input + pos, rank);
                            omega *= unit_omega;
                        }
                    }
                }
            }
            // 基4快速傅里叶变换,模板,学习用
            void fft_radix4_dit(Complex *input, size_t fft_len)
            {
                size_t log4_len = hint_log2(fft_len) / 2;
                fft_len = 1ull << (log4_len * 2);
                quaternary_reverse_swap(input, fft_len);
                for (size_t pos = 0; pos < fft_len; pos += 4)
                {
                    fft_4point(input + pos, 1);
                }
                for (size_t rank = 4; rank < fft_len; rank *= 4)
                {
                    // rank表示上一级fft的长度,gap表示由四个上一级可以迭代计算出这一级的长度
                    size_t gap = rank * 4;
                    Complex unit_omega = std::polar<HintFloat>(1, -HINT_2PI / gap);
                    Complex unit_sqr = std::polar<HintFloat>(1, -HINT_2PI * 2 / gap);
                    Complex unit_cube = std::polar<HintFloat>(1, -HINT_2PI * 3 / gap);
                    for (size_t begin = 0; begin < fft_len; begin += gap)
                    {
                        fft_4point(input + begin, rank);
                        Complex omega = unit_omega;
                        Complex omega_sqr = unit_sqr;
                        Complex omega_cube = unit_cube;
                        for (size_t pos = begin + 1; pos < begin + rank; pos++)
                        {
                            fft_radix4_dit_butterfly(omega, omega_sqr, omega_cube, input + pos, rank);
                            omega *= unit_omega;
                            omega_sqr *= unit_sqr;
                            omega_cube *= unit_cube;
                        }
                    }
                }
            }
            // 基2查表时间抽取FFT
            void fft_radix2_dit_lut(Complex *input, size_t fft_len, bool bit_rev = true)
            {
                if (fft_len <= 1)
                {
                    return;
                }
                if (fft_len == 2)
                {
                    fft_2point(input[0], input[1]);
                    return;
                }
                if (bit_rev)
                {
                    binary_reverse_swap(input, fft_len);
                }
                TABLE.expand(hint_log2(fft_len));
                for (size_t i = 0; i < fft_len; i += 2)
                {
                    fft_2point(input[i], input[i + 1]);
                }
                INT_32 log_len = 2;
                for (size_t rank = 2; rank < fft_len / 2; rank *= 2)
                {
                    size_t gap = rank * 2;
                    for (size_t begin = 0; begin < fft_len; begin += gap)
                    {
                        fft_2point(input[begin], input[begin + rank]);
                        for (size_t pos = begin + 1; pos < begin + rank; pos++)
                        {
                            Complex omega = TABLE.get_omega(log_len, pos - begin);
                            fft_radix2_dit_butterfly(omega, input + pos, rank);
                        }
                    }
                    log_len++;
                }
                fft_len /= 2;
                for (size_t pos = 0; pos < fft_len; pos++)
                {
                    Complex omega = TABLE.get_omega(log_len, pos);
                    fft_radix2_dit_butterfly(omega, input + pos, fft_len);
                }
            }
            // 基2查表频率抽取FFT
            void fft_radix2_dif_lut(Complex *input, size_t fft_len, const bool bit_rev = true)
            {
                if (fft_len <= 1)
                {
                    return;
                }
                if (fft_len == 2)
                {
                    fft_2point(input[0], input[1]);
                    return;
                }
                INT_32 log_len = hint_log2(fft_len);
                TABLE.expand(log_len);
                fft_len /= 2;
                for (size_t pos = 0; pos < fft_len; pos++)
                {
                    Complex omega = TABLE.get_omega(log_len, pos);
                    fft_radix2_dif_butterfly(omega, input + pos, fft_len);
                }
                fft_len *= 2;
                log_len--;
                for (size_t rank = fft_len / 4; rank > 1; rank /= 2)
                {
                    size_t gap = rank * 2;
                    for (size_t begin = 0; begin < fft_len; begin += gap)
                    {
                        fft_2point(input[begin], input[begin + rank]);
                        for (size_t pos = begin + 1; pos < begin + rank; pos++)
                        {
                            Complex omega = TABLE.get_omega(log_len, pos - begin);
                            fft_radix2_dif_butterfly(omega, input + pos, rank);
                        }
                    }
                    log_len--;
                }
                for (size_t i = 0; i < fft_len; i += 2)
                {
                    fft_2point(input[i], input[i + 1]);
                }
                if (bit_rev)
                {
                    binary_reverse_swap(input, fft_len);
                }
            }
            // 模板化时间抽取分裂基fft
            template <size_t LEN>
            void fft_split_radix_dit_template(Complex *input)
            {
                constexpr size_t log_len = hint_log2(LEN);
                constexpr size_t half_len = LEN / 2, quarter_len = LEN / 4;
                fft_split_radix_dit_template<half_len>(input);
                fft_split_radix_dit_template<quarter_len>(input + half_len);
                fft_split_radix_dit_template<quarter_len>(input + half_len + quarter_len);
                for (size_t i = 0; i < quarter_len; i++)
                {
                    Complex omega = TABLE.get_omega(log_len, i);
                    Complex omega_cube = TABLE.get_omega(log_len, i * 3);
                    fft_split_radix_dit_butterfly(omega, omega_cube, input + i, quarter_len);
                }
            }
            template <>
            void fft_split_radix_dit_template<0>(Complex *input) {}
            template <>
            void fft_split_radix_dit_template<1>(Complex *input) {}
            template <>
            void fft_split_radix_dit_template<2>(Complex *input)
            {
                fft_2point(input[0], input[1]);
            }
            template <>
            void fft_split_radix_dit_template<4>(Complex *input)
            {
                fft_dit_4point(input, 1);
            }
            template <>
            void fft_split_radix_dit_template<8>(Complex *input)
            {
                fft_dit_8point(input, 1);
            }
            template <>
            void fft_split_radix_dit_template<16>(Complex *input)
            {
                fft_dit_16point(input, 1);
            }
            template <>
            void fft_split_radix_dit_template<32>(Complex *input)
            {
                fft_dit_32point(input, 1);
            }

            // 模板化频率抽取分裂基fft
            template <size_t LEN>
            void fft_split_radix_dif_template(Complex *input)
            {
                constexpr size_t log_len = hint_log2(LEN);
                constexpr size_t half_len = LEN / 2, quarter_len = LEN / 4;
                for (size_t i = 0; i < quarter_len; i++)
                {
                    Complex omega = TABLE.get_omega(log_len, i);
                    Complex omega_cube = TABLE.get_omega(log_len, i * 3);
                    fft_split_radix_dif_butterfly(omega, omega_cube, input + i, quarter_len);
                }
                fft_split_radix_dif_template<half_len>(input);
                fft_split_radix_dif_template<quarter_len>(input + half_len);
                fft_split_radix_dif_template<quarter_len>(input + half_len + quarter_len);
            }
            template <>
            void fft_split_radix_dif_template<0>(Complex *input) {}
            template <>
            void fft_split_radix_dif_template<1>(Complex *input) {}
            template <>
            void fft_split_radix_dif_template<2>(Complex *input)
            {
                fft_2point(input[0], input[1]);
            }
            template <>
            void fft_split_radix_dif_template<4>(Complex *input)
            {
                fft_dif_4point(input, 1);
            }
            template <>
            void fft_split_radix_dif_template<8>(Complex *input)
            {
                fft_dif_8point(input, 1);
            }
            template <>
            void fft_split_radix_dif_template<16>(Complex *input)
            {
                fft_dif_16point(input, 1);
            }
            template <>
            void fft_split_radix_dif_template<32>(Complex *input)
            {
                fft_dif_32point(input, 1);
            }

            // 辅助选择函数
            template <size_t LEN = 1>
            void fft_split_radix_dit_template_alt(Complex *input, size_t fft_len)
            {
                if (fft_len < LEN)
                {
                    fft_split_radix_dit_template_alt<LEN / 2>(input, fft_len);
                    return;
                }
                TABLE.expand(hint_log2(LEN));
                fft_split_radix_dit_template<LEN>(input);
            }
            template <>
            void fft_split_radix_dit_template_alt<0>(Complex *input, size_t fft_len) {}

            // 辅助选择函数
            template <size_t LEN = 1>
            void fft_split_radix_dif_template_alt(Complex *input, size_t fft_len)
            {
                if (fft_len < LEN)
                {
                    fft_split_radix_dif_template_alt<LEN / 2>(input, fft_len);
                    return;
                }
                TABLE.expand(hint_log2(LEN));
                fft_split_radix_dif_template<LEN>(input);
            }
            template <>
            void fft_split_radix_dif_template_alt<0>(Complex *input, size_t fft_len) {}

            auto fft_split_radix_dit = fft_split_radix_dit_template_alt<size_t(1) << lut_max_rank>;
            auto fft_split_radix_dif = fft_split_radix_dif_template_alt<size_t(1) << lut_max_rank>;

            /// @brief 时间抽取基2fft
            /// @param input 复数组
            /// @param fft_len 数组长度
            /// @param bit_rev 是否逆序
            inline void fft_dit(Complex *input, size_t fft_len, bool bit_rev = true)
            {
                fft_len = max_2pow(fft_len);
                if (bit_rev)
                {
                    binary_reverse_swap(input, fft_len);
                }
                fft_split_radix_dit(input, fft_len);
            }

            /// @brief 频率抽取基2fft
            /// @param input 复数组
            /// @param fft_len 数组长度
            /// @param bit_rev 是否逆序
            inline void fft_dif(Complex *input, size_t fft_len, bool bit_rev = true)
            {
                fft_len = max_2pow(fft_len);
                fft_split_radix_dif(input, fft_len);
                if (bit_rev)
                {
                    binary_reverse_swap(input, fft_len);
                }
            }

            /// @brief fft正变换
            /// @param input 复数组
            /// @param fft_len 变换长度
            inline void fft(Complex *input, size_t fft_len)
            {
                size_t log_len = hint_log2(fft_len);
                fft_len = 1ull << log_len;
                if (fft_len <= 1)
                {
                    return;
                }
                fft_dif(input, fft_len, true);
            }

            /// @brief fft逆变换
            /// @param input 复数组
            /// @param fft_len 变换长度
            inline void ifft(Complex *input, size_t fft_len)
            {
                size_t log_len = hint_log2(fft_len);
                fft_len = 1ull << log_len;
                if (fft_len <= 1)
                {
                    return;
                }
                fft_len = max_2pow(fft_len);
                fft_conj(input, fft_len);
                fft_dit(input, fft_len, true);
                fft_conj(input, fft_len, fft_len);
            }
#if MULTITHREAD == 1
            void fft_dit_2ths(Complex *input, size_t fft_len)
            {
                if (fft_len <= 8)
                {
                    fft_dit(input, fft_len);
                    return;
                }
                const size_t half_len = fft_len / 2;
                const INT_32 log_len = hint_log2(fft_len);
                TABLE.expand(log_len);
                auto th = std::async(fft_dit, input, half_len, false);
                fft_dit(input + half_len, half_len, false);
                th.wait();
                auto proc = [&](size_t start, size_t end)
                {
                    for (size_t i = start; i < end; i++)
                    {
                        Complex omega = TABLE.get_omega(log_len, i);
                        fft_radix2_dit_butterfly(omega, input + i, half_len);
                    }
                };
                th = std::async(proc, 0, half_len / 2);
                proc(half_len / 2, half_len);
                th.wait();
            }
            void fft_dif_2ths(Complex *input, size_t fft_len)
            {
                if (fft_len <= 8)
                {
                    fft_dif(input, fft_len);
                    return;
                }
                const size_t half_len = fft_len / 2;
                const INT_32 log_len = hint_log2(fft_len);
                TABLE.expand(log_len);
                auto proc = [&](size_t start, size_t end)
                {
                    for (size_t i = start; i < end; i++)
                    {
                        Complex omega = TABLE.get_omega(log_len, i);
                        fft_radix2_dif_butterfly(omega, input + i, half_len);
                    }
                };
                auto th = std::async(proc, 0, half_len / 2);
                proc(half_len / 2, half_len);
                th.wait();
                th = std::async(fft_dif, input, half_len, false);
                fft_dif(input + half_len, half_len, false);
                th.wait();
            }
            void fft_dit_4ths(Complex *input, size_t fft_len)
            {
                if (fft_len <= 8)
                {
                    fft_dit(input, fft_len);
                    return;
                }
                const size_t half_len = fft_len / 2;
                const INT_32 log_len = hint_log2(fft_len);
                TABLE.expand(log_len);
                auto th1 = std::async(fft_dit_2ths, input, half_len);
                fft_dit_2ths(input + half_len, half_len);
                th1.wait();

                auto proc = [&](size_t start, size_t end)
                {
                    for (size_t i = start; i < end; i++)
                    {
                        Complex omega = TABLE.get_omega(log_len, i);
                        fft_radix2_dit_butterfly(omega, input + i, half_len);
                    }
                };
                const size_t sub_len = fft_len / 8;
                th1 = std::async(proc, 0, sub_len);
                auto th2 = std::async(proc, sub_len, sub_len * 2);
                auto th3 = std::async(proc, sub_len * 2, sub_len * 3);
                proc(sub_len * 3, sub_len * 4);
                th1.wait();
                th2.wait();
                th3.wait();
            }
            void fft_dif_4ths(Complex *input, size_t fft_len)
            {
                if (fft_len <= 8)
                {
                    fft_dif(input, fft_len);
                    return;
                }
                const size_t half_len = fft_len / 2;
                const INT_32 log_len = hint_log2(fft_len);
                TABLE.expand(log_len);
                auto proc = [&](size_t start, size_t end)
                {
                    for (size_t i = start; i < end; i++)
                    {
                        Complex omega = TABLE.get_omega(log_len, i);
                        fft_radix2_dif_butterfly(omega, input + i, half_len);
                    }
                };
                const size_t sub_len = fft_len / 8;
                auto th1 = std::async(proc, 0, sub_len);
                auto th2 = std::async(proc, sub_len, sub_len * 2);
                auto th3 = std::async(proc, sub_len * 2, sub_len * 3);
                proc(sub_len * 3, sub_len * 4);
                th1.wait();
                th2.wait();
                th3.wait();

                th1 = std::async(fft_dif_2ths, input, half_len);
                fft_dif_2ths(input + half_len, half_len);
                th1.wait();
            }
#endif
        }
        namespace hint_fht
        {
            /// @brief 快速哈特莱变换
            /// @param input 浮点数组指针
            /// @param fht_len 变换的长度
            /// @param is_ifht 是否为逆变换
            void fht(HintFloat *input, size_t fht_len)
            {
                fht_len = max_2pow(fht_len);
                if (fht_len <= 1)
                {
                    return;
                }
                UINT_32 log_len = hint_log2(fht_len);
                hint_fft::TABLE.expand(log_len);
                binary_reverse_swap(input, fht_len);
                for (size_t i = 0; i < fht_len; i += 2)
                {
                    HintFloat tmp1 = input[i];
                    HintFloat tmp2 = input[i + 1];
                    input[i] = tmp1 + tmp2;
                    input[i + 1] = tmp1 - tmp2;
                }
                UINT_32 shift = 2;
                for (size_t rank = 2; rank < fht_len; rank *= 2)
                {
                    size_t gap = rank * 2;
                    size_t half = rank / 2;
                    for (size_t begin = 0; begin < fht_len; begin += gap)
                    {
                        size_t index1 = begin, index2 = begin + half;
                        size_t index3 = begin + rank, index4 = begin + half * 3;
                        HintFloat tmp1 = input[index1];
                        HintFloat tmp2 = input[index3];
                        input[index1] = tmp1 + tmp2;
                        input[index3] = tmp1 - tmp2;
                        tmp1 = input[index2];
                        tmp2 = input[index4];
                        input[index2] = tmp1 + tmp2;
                        input[index4] = tmp1 - tmp2;
                        for (size_t pos = 1; pos < half; pos++)
                        {
                            index1 = begin + pos;
                            index2 = rank + begin - pos;
                            index3 = rank + begin + pos;
                            index4 = gap + begin - pos;

                            HintFloat tmp1 = input[index1];
                            HintFloat tmp2 = input[index2];
                            HintFloat tmp3 = input[index3];
                            HintFloat tmp4 = input[index4];

                            Complex omega = std::conj(hint_fft::TABLE.get_omega(shift, pos));
                            HintFloat t1 = tmp3 * omega.real() + tmp4 * omega.imag();
                            HintFloat t2 = tmp3 * omega.imag() - tmp4 * omega.real();

                            input[index1] = tmp1 + t1;
                            input[index2] = tmp2 + t2;
                            input[index3] = tmp1 - t1;
                            input[index4] = tmp2 - t2;
                        }
                    }
                    shift++;
                }
            }
            void ifht(HintFloat *input, size_t fht_len)
            {
                fht_len = max_2pow(fht_len);
                fht(input, fht_len);
                HintFloat len = fht_len;
                for (size_t i = 0; i < fht_len; i++)
                {
                    input[i] /= len;
                }
            }
        }
        namespace hint_ntt
        {
            template <typename DataTy, UINT_64 MOD>
            struct ModInt
            {
                // 实际存放的整数
                DataTy data = 0;
                // 等价复数的i
                constexpr ModInt() noexcept {}
                constexpr ModInt(DataTy num) noexcept
                {
                    data = num;
                }
                constexpr ModInt operator+(ModInt n) const
                {
                    UINT_64 sum = UINT_64(data) + n.data;
                    return sum < MOD ? sum : sum - MOD;
                }
                constexpr ModInt operator-(ModInt n) const
                {
                    return data < n.data ? MOD + data - n.data : data - n.data;
                }
                constexpr ModInt operator*(ModInt n) const
                {
                    return static_cast<UINT_64>(data) * n.data % MOD;
                }
                constexpr ModInt operator/(ModInt n) const
                {
                    return *this * inv();
                }
                constexpr ModInt inv() const
                {
                    return qpow(*this, MOD - 2u);
                }
                constexpr static UINT_64 mod()
                {
                    return MOD;
                }
            };
            template <UINT_64 MOD>
            struct ModInt<UINT_64, MOD>
            {
                // 实际存放的整数
                UINT_64 data = 0;
                // 等价复数的i
                constexpr ModInt() noexcept {}
                constexpr ModInt(UINT_64 num) noexcept
                {
                    data = num;
                }
                constexpr ModInt operator+(ModInt n) const
                {
                    return (n.data += data) < MOD ? n.data : n.data - MOD;
                }
                constexpr ModInt operator-(ModInt n) const
                {
                    return data < n.data ? MOD + data - n.data : data - n.data;
                }
                constexpr ModInt operator*(ModInt n) const
                {
                    UINT_64 b1 = n.data & 0xffff;
                    UINT_64 b2 = (n.data >> 16) & 0xffff;
                    UINT_64 b3 = n.data >> 32;
                    b1 = data * b1;
                    b2 = data * b2;
                    b3 = (((data * b3) % MOD) << 16) + b2;
                    b3 = ((b3 % MOD) << 16) + b1;
                    return b3 % MOD;
                    // UINT_64 b2 = n.data >> 20;
                    // n.data &= 0xfffff;
                    // n.data *= data;
                    // b2 = data * b2 % MOD;
                    // return (n.data + (b2 << 20)) % MOD;
                }
                constexpr ModInt operator/(ModInt n) const
                {
                    return *this * inv();
                }
                constexpr ModInt inv() const
                {
                    return qpow(*this, MOD - 2ull);
                }
                constexpr static UINT_64 mod()
                {
                    return MOD;
                }
            };
            template <UINT_64 MOD, UINT_64 ROOT>
            struct NTT_BASIC
            {
                static constexpr UINT_64 mod()
                {
                    return MOD;
                }
                static constexpr UINT_64 root()
                {
                    return ROOT;
                }

                using NTTModInt32 = ModInt<UINT_32, MOD>;
                using NTTModInt64 = ModInt<UINT_64, MOD>;

                template <typename T>
                static constexpr void ntt_normalize(T *input, size_t ntt_len)
                {
                    const T inv = T(ntt_len).inv();
                    size_t mod4 = ntt_len % 4;
                    ntt_len -= mod4;
                    for (size_t i = 0; i < ntt_len; i += 4)
                    {
                        input[i] = inv * input[i];
                        input[i + 1] = inv * input[i + 1];
                        input[i + 2] = inv * input[i + 2];
                        input[i + 3] = inv * input[i + 3];
                    }
                    for (size_t i = ntt_len; i < ntt_len + mod4; i++)
                    {
                        input[i] = inv * input[i];
                    }
                }
                // 2点NTT
                template <typename T>
                static constexpr void ntt_2point(T &sum, T &diff)
                {
                    T tmp1 = sum;
                    T tmp2 = diff;
                    sum = tmp1 + tmp2;
                    diff = tmp1 - tmp2;
                }
                template <typename T>
                static constexpr void ntt_dit_4point(T *input, size_t rank = 1)
                {
                    constexpr T W_4_1 = qpow(T(ROOT), (MOD - 1) / 4); // 等价于复数i
                    T tmp0 = input[0];
                    T tmp1 = input[rank];
                    T tmp2 = input[rank * 2];
                    T tmp3 = input[rank * 3];

                    ntt_2point(tmp0, tmp1);
                    ntt_2point(tmp2, tmp3);
                    tmp3 = tmp3 * W_4_1;

                    input[0] = tmp0 + tmp2;
                    input[rank] = tmp1 + tmp3;
                    input[rank * 2] = tmp0 - tmp2;
                    input[rank * 3] = tmp1 - tmp3;
                }
                template <typename T>
                static constexpr void ntt_dit_8point(T *input, size_t rank = 1)
                {
                    constexpr T W_8_1 = qpow(T(ROOT), (MOD - 1) / 8);
                    constexpr T W_8_2 = qpow(W_8_1, 2);
                    constexpr T W_8_3 = qpow(W_8_1, 3);
                    T tmp0 = input[0];
                    T tmp1 = input[rank];
                    T tmp2 = input[rank * 2];
                    T tmp3 = input[rank * 3];
                    T tmp4 = input[rank * 4];
                    T tmp5 = input[rank * 5];
                    T tmp6 = input[rank * 6];
                    T tmp7 = input[rank * 7];
                    ntt_2point(tmp0, tmp1);
                    ntt_2point(tmp2, tmp3);
                    ntt_2point(tmp4, tmp5);
                    ntt_2point(tmp6, tmp7);
                    tmp3 = tmp3 * W_8_2;
                    tmp7 = tmp7 * W_8_2;

                    ntt_2point(tmp0, tmp2);
                    ntt_2point(tmp1, tmp3);
                    ntt_2point(tmp4, tmp6);
                    ntt_2point(tmp5, tmp7);
                    tmp5 = tmp5 * W_8_1;
                    tmp6 = tmp6 * W_8_2;
                    tmp7 = tmp7 * W_8_3;

                    input[0] = tmp0 + tmp4;
                    input[rank] = tmp1 + tmp5;
                    input[rank * 2] = tmp2 + tmp6;
                    input[rank * 3] = tmp3 + tmp7;
                    input[rank * 4] = tmp0 - tmp4;
                    input[rank * 5] = tmp1 - tmp5;
                    input[rank * 6] = tmp2 - tmp6;
                    input[rank * 7] = tmp3 - tmp7;
                }
                template <typename T>
                static constexpr void ntt_dit_16point(T *input, size_t rank = 1)
                {
                    constexpr T W_16_1 = qpow(T(ROOT), (MOD - 1) / 16);
                    constexpr T W_16_2 = qpow(W_16_1, 2);
                    constexpr T W_16_3 = qpow(W_16_1, 3);
                    constexpr T W_16_4 = qpow(W_16_1, 4);
                    constexpr T W_16_5 = qpow(W_16_1, 5);
                    constexpr T W_16_6 = qpow(W_16_1, 6);
                    constexpr T W_16_7 = qpow(W_16_1, 7);

                    ntt_dit_8point(input, rank);
                    ntt_dit_8point(input + rank * 8, rank);

                    T tmp0 = input[0];
                    T tmp1 = input[rank];
                    T tmp2 = input[rank * 8];
                    T tmp3 = input[rank * 9] * W_16_1;
                    input[0] = tmp0 + tmp2;
                    input[rank] = tmp1 + tmp3;
                    input[rank * 8] = tmp0 - tmp2;
                    input[rank * 9] = tmp1 - tmp3;

                    tmp0 = input[rank * 2];
                    tmp1 = input[rank * 3];
                    tmp2 = input[rank * 10] * W_16_2;
                    tmp3 = input[rank * 11] * W_16_3;
                    input[rank * 2] = tmp0 + tmp2;
                    input[rank * 3] = tmp1 + tmp3;
                    input[rank * 10] = tmp0 - tmp2;
                    input[rank * 11] = tmp1 - tmp3;

                    tmp0 = input[rank * 4];
                    tmp1 = input[rank * 5];
                    tmp2 = input[rank * 12] * W_16_4;
                    tmp3 = input[rank * 13] * W_16_5;
                    input[rank * 4] = tmp0 + tmp2;
                    input[rank * 5] = tmp1 + tmp3;
                    input[rank * 12] = tmp0 - tmp2;
                    input[rank * 13] = tmp1 - tmp3;

                    tmp0 = input[rank * 6];
                    tmp1 = input[rank * 7];
                    tmp2 = input[rank * 14] * W_16_6;
                    tmp3 = input[rank * 15] * W_16_7;
                    input[rank * 6] = tmp0 + tmp2;
                    input[rank * 7] = tmp1 + tmp3;
                    input[rank * 14] = tmp0 - tmp2;
                    input[rank * 15] = tmp1 - tmp3;
                }
                template <typename T>
                static constexpr void ntt_dif_4point(T *input, size_t rank = 1)
                {
                    constexpr T W_4_1 = qpow(T(ROOT), (MOD - 1) / 4);
                    T tmp0 = input[0];
                    T tmp1 = input[rank];
                    T tmp2 = input[rank * 2];
                    T tmp3 = input[rank * 3];

                    ntt_2point(tmp0, tmp2);
                    ntt_2point(tmp1, tmp3);
                    tmp3 = tmp3 * W_4_1;

                    input[0] = tmp0 + tmp1;
                    input[rank] = tmp0 - tmp1;
                    input[rank * 2] = tmp2 + tmp3;
                    input[rank * 3] = tmp2 - tmp3;
                }
                template <typename T>
                static constexpr void ntt_dif_8point(T *input, size_t rank = 1)
                {
                    constexpr T W_8_1 = qpow(T(ROOT), (MOD - 1) / 8);
                    constexpr T W_8_2 = qpow(W_8_1, 2);
                    constexpr T W_8_3 = qpow(W_8_1, 3);
                    T tmp0 = input[0];
                    T tmp1 = input[rank];
                    T tmp2 = input[rank * 2];
                    T tmp3 = input[rank * 3];
                    T tmp4 = input[rank * 4];
                    T tmp5 = input[rank * 5];
                    T tmp6 = input[rank * 6];
                    T tmp7 = input[rank * 7];

                    ntt_2point(tmp0, tmp4);
                    ntt_2point(tmp1, tmp5);
                    ntt_2point(tmp2, tmp6);
                    ntt_2point(tmp3, tmp7);
                    tmp5 = tmp5 * W_8_1;
                    tmp6 = tmp6 * W_8_2;
                    tmp7 = tmp7 * W_8_3;

                    ntt_2point(tmp0, tmp2);
                    ntt_2point(tmp1, tmp3);
                    ntt_2point(tmp4, tmp6);
                    ntt_2point(tmp5, tmp7);
                    tmp3 = tmp3 * W_8_2;
                    tmp7 = tmp7 * W_8_2;

                    input[0] = tmp0 + tmp1;
                    input[rank] = tmp0 - tmp1;
                    input[rank * 2] = tmp2 + tmp3;
                    input[rank * 3] = tmp2 - tmp3;
                    input[rank * 4] = tmp4 + tmp5;
                    input[rank * 5] = tmp4 - tmp5;
                    input[rank * 6] = tmp6 + tmp7;
                    input[rank * 7] = tmp6 - tmp7;
                }
                template <typename T>
                static constexpr void ntt_dif_16point(T *input, size_t rank = 1)
                {
                    constexpr T W_16_1 = qpow(T(ROOT), (MOD - 1) / 16);
                    constexpr T W_16_2 = qpow(W_16_1, 2);
                    constexpr T W_16_3 = qpow(W_16_1, 3);
                    constexpr T W_16_4 = qpow(W_16_1, 4);
                    constexpr T W_16_5 = qpow(W_16_1, 5);
                    constexpr T W_16_6 = qpow(W_16_1, 6);
                    constexpr T W_16_7 = qpow(W_16_1, 7);

                    T tmp0 = input[0];
                    T tmp1 = input[rank];
                    T tmp2 = input[rank * 8];
                    T tmp3 = input[rank * 9];
                    input[0] = tmp0 + tmp2;
                    input[rank] = tmp1 + tmp3;
                    input[rank * 8] = tmp0 - tmp2;
                    input[rank * 9] = (tmp1 - tmp3) * W_16_1;

                    tmp0 = input[rank * 2];
                    tmp1 = input[rank * 3];
                    tmp2 = input[rank * 10];
                    tmp3 = input[rank * 11];
                    input[rank * 2] = tmp0 + tmp2;
                    input[rank * 3] = tmp1 + tmp3;
                    input[rank * 10] = (tmp0 - tmp2) * W_16_2;
                    input[rank * 11] = (tmp1 - tmp3) * W_16_3;

                    tmp0 = input[rank * 4];
                    tmp1 = input[rank * 5];
                    tmp2 = input[rank * 12];
                    tmp3 = input[rank * 13];
                    input[rank * 4] = tmp0 + tmp2;
                    input[rank * 5] = tmp1 + tmp3;
                    input[rank * 12] = (tmp0 - tmp2) * W_16_4;
                    input[rank * 13] = (tmp1 - tmp3) * W_16_5;

                    tmp0 = input[rank * 6];
                    tmp1 = input[rank * 7];
                    tmp2 = input[rank * 14];
                    tmp3 = input[rank * 15];
                    input[rank * 6] = tmp0 + tmp2;
                    input[rank * 7] = tmp1 + tmp3;
                    input[rank * 14] = (tmp0 - tmp2) * W_16_6;
                    input[rank * 15] = (tmp1 - tmp3) * W_16_7;

                    ntt_dif_8point(input, rank);
                    ntt_dif_8point(input + rank * 8, rank);
                }
                // 基2时间抽取ntt蝶形
                template <typename T>
                static constexpr void ntt_radix2_dit_butterfly(T omega, T *input, size_t rank)
                {
                    T tmp1 = input[0];
                    T tmp2 = input[rank] * omega;
                    input[0] = tmp1 + tmp2;
                    input[rank] = tmp1 - tmp2;
                }
                // 基2频率抽取ntt蝶形
                template <typename T>
                static constexpr void ntt_radix2_dif_butterfly(T omega, T *input, size_t rank)
                {
                    T tmp1 = input[0];
                    T tmp2 = input[rank];
                    input[0] = tmp1 + tmp2;
                    input[rank] = (tmp1 - tmp2) * omega;
                }
                // ntt分裂基时间抽取蝶形变换
                template <typename T>
                static constexpr void ntt_split_radix_dit_butterfly(T omega, T omega_cube,
                                                                    T *input, size_t rank)
                {
                    constexpr T W_4_1 = qpow(T(ROOT), (MOD - 1) / 4); // 等价于复数i
                    T tmp0 = input[0];
                    T tmp1 = input[rank];
                    T tmp2 = input[rank * 2] * omega;
                    T tmp3 = input[rank * 3] * omega_cube;

                    ntt_2point(tmp2, tmp3);
                    tmp3 = tmp3 * W_4_1;

                    input[0] = tmp0 + tmp2;
                    input[rank] = tmp1 + tmp3;
                    input[rank * 2] = tmp0 - tmp2;
                    input[rank * 3] = tmp1 - tmp3;
                }
                // ntt分裂基频率抽取蝶形变换
                template <typename T>
                static constexpr void ntt_split_radix_dif_butterfly(T omega, T omega_cube,
                                                                    T *input, size_t rank)
                {
                    constexpr T W_4_1 = qpow(T(ROOT), (MOD - 1) / 4); // 等价于复数i
                    T tmp0 = input[0];
                    T tmp1 = input[rank];
                    T tmp2 = input[rank * 2];
                    T tmp3 = input[rank * 3];

                    ntt_2point(tmp0, tmp2);
                    ntt_2point(tmp1, tmp3);
                    tmp3 = tmp3 * W_4_1;

                    input[0] = tmp0;
                    input[rank] = tmp1;
                    input[rank * 2] = (tmp2 + tmp3) * omega;
                    input[rank * 3] = (tmp2 - tmp3) * omega_cube;
                }
            };
            // 模板递归分裂基NTT
            template <size_t LEN, UINT_64 MOD, UINT_64 ROOT>
            struct SPLIT_RADIX_NTT
            {
                using ntt_basic = NTT_BASIC<MOD, ROOT>;
                static constexpr size_t half_len = LEN / 2, quarter_len = LEN / 4;
                // 模板化时间抽取分裂基ntt
                template <typename T>
                static constexpr void ntt_split_radix_dit_template(T input[])
                {
                    SPLIT_RADIX_NTT<half_len, MOD, ROOT>::ntt_split_radix_dit_template(input);
                    SPLIT_RADIX_NTT<quarter_len, MOD, ROOT>::ntt_split_radix_dit_template(input + half_len);
                    SPLIT_RADIX_NTT<quarter_len, MOD, ROOT>::ntt_split_radix_dit_template(input + half_len + quarter_len);
                    constexpr T unit = qpow(T(ROOT), (MOD - 1) / LEN);
                    constexpr T unit_cube = qpow(unit, 3);
                    T omega(1), omega_cube(1);
                    for (size_t i = 0; i < quarter_len; i++)
                    {
                        ntt_basic::ntt_split_radix_dit_butterfly(omega, omega_cube, input + i, quarter_len);
                        omega = omega * unit;
                        omega_cube = omega_cube * unit_cube;
                    }
                }
                // 模板化频率抽取分裂基ntt
                template <typename T>
                static constexpr void ntt_split_radix_dif_template(T input[])
                {
                    constexpr T unit = qpow(T(ROOT), (MOD - 1) / LEN);
                    constexpr T unit_cube = qpow(unit, 3);
                    T omega(1), omega_cube(1);
                    for (size_t i = 0; i < quarter_len; i++)
                    {
                        ntt_basic::ntt_split_radix_dif_butterfly(omega, omega_cube, input + i, quarter_len);
                        omega = omega * unit;
                        omega_cube = omega_cube * unit_cube;
                    }
                    SPLIT_RADIX_NTT<half_len, MOD, ROOT>::ntt_split_radix_dif_template(input);
                    SPLIT_RADIX_NTT<quarter_len, MOD, ROOT>::ntt_split_radix_dif_template(input + half_len);
                    SPLIT_RADIX_NTT<quarter_len, MOD, ROOT>::ntt_split_radix_dif_template(input + half_len + quarter_len);
                }
            };
            template <UINT_64 MOD, UINT_64 ROOT>
            struct SPLIT_RADIX_NTT<0, MOD, ROOT>
            {
                template <typename T>
                static constexpr void ntt_split_radix_dit_template(T input[]) {}
                template <typename T>
                static constexpr void ntt_split_radix_dif_template(T input[]) {}
            };
            template <UINT_64 MOD, UINT_64 ROOT>
            struct SPLIT_RADIX_NTT<1, MOD, ROOT>
            {
                template <typename T>
                static constexpr void ntt_split_radix_dit_template(T input[]) {}
                template <typename T>
                static constexpr void ntt_split_radix_dif_template(T input[]) {}
            };
            template <UINT_64 MOD, UINT_64 ROOT>
            struct SPLIT_RADIX_NTT<2, MOD, ROOT>
            {
                using ntt_basic = NTT_BASIC<MOD, ROOT>;
                template <typename T>
                static constexpr void ntt_split_radix_dit_template(T input[])
                {
                    ntt_basic::ntt_2point(input[0], input[1]);
                }
                template <typename T>
                static constexpr void ntt_split_radix_dif_template(T input[])
                {
                    ntt_basic::ntt_2point(input[0], input[1]);
                }
            };
            template <UINT_64 MOD, UINT_64 ROOT>
            struct SPLIT_RADIX_NTT<4, MOD, ROOT>
            {
                using ntt_basic = NTT_BASIC<MOD, ROOT>;
                template <typename T>
                static constexpr void ntt_split_radix_dit_template(T input[])
                {
                    ntt_basic::ntt_dit_4point(input, 1);
                }
                template <typename T>
                static constexpr void ntt_split_radix_dif_template(T input[])
                {
                    ntt_basic::ntt_dif_4point(input, 1);
                }
            };
            template <UINT_64 MOD, UINT_64 ROOT>
            struct SPLIT_RADIX_NTT<8, MOD, ROOT>
            {
                using ntt_basic = NTT_BASIC<MOD, ROOT>;
                template <typename T>
                static constexpr void ntt_split_radix_dit_template(T input[])
                {
                    ntt_basic::ntt_dit_8point(input, 1);
                }
                template <typename T>
                static constexpr void ntt_split_radix_dif_template(T input[])
                {
                    ntt_basic::ntt_dif_8point(input, 1);
                }
            };
            template <UINT_64 MOD, UINT_64 ROOT>
            struct SPLIT_RADIX_NTT<16, MOD, ROOT>
            {
                using ntt_basic = NTT_BASIC<MOD, ROOT>;
                template <typename T>
                static constexpr void ntt_split_radix_dit_template(T input[])
                {
                    ntt_basic::ntt_dit_16point(input, 1);
                }
                template <typename T>
                static constexpr void ntt_split_radix_dif_template(T input[])
                {
                    ntt_basic::ntt_dif_16point(input, 1);
                }
            };
            // 分裂基辅助选择类
            template <size_t LEN, UINT_64 MOD, UINT_64 ROOT>
            struct NTT_ALT
            {
                template <typename T>
                static constexpr void ntt_dit_template(T input[], size_t ntt_len)
                {
                    if (ntt_len < LEN)
                    {
                        NTT_ALT<LEN / 2, MOD, ROOT>::ntt_dit_template(input, ntt_len);
                        return;
                    }
                    SPLIT_RADIX_NTT<LEN, MOD, ROOT>::ntt_split_radix_dit_template(input);
                }
                template <typename T>
                static constexpr void ntt_dif_template(T input[], size_t ntt_len)
                {
                    if (ntt_len < LEN)
                    {
                        NTT_ALT<LEN / 2, MOD, ROOT>::ntt_dif_template(input, ntt_len);
                        return;
                    }
                    SPLIT_RADIX_NTT<LEN, MOD, ROOT>::ntt_split_radix_dif_template(input);
                }
            };
            template <UINT_64 MOD, UINT_64 ROOT>
            struct NTT_ALT<0, MOD, ROOT>
            {
                template <typename T>
                static constexpr void ntt_dit_template(T input[], size_t ntt_len) {}
                template <typename T>
                static constexpr void ntt_dif_template(T input[], size_t ntt_len) {}
            };
            // 快速数论变换主类
            template <UINT_64 MOD, UINT_64 ROOT, size_t MAX_LEN = 1 << 23>
            struct NTT
            {
                using ntt_basic = NTT_BASIC<MOD, ROOT>;
                using NTTModInt32 = ModInt<UINT_32, MOD>;
                using NTTModInt64 = ModInt<UINT_64, MOD>;
                static constexpr UINT_64 mod()
                {
                    return MOD;
                }
                static constexpr UINT_64 root()
                {
                    return ROOT;
                }
                static constexpr UINT_64 iroot()
                {
                    return NTTModInt64(ROOT).inv().data;
                }
                // 基2时间抽取ntt,学习用
                template <typename T>
                static void ntt_radix2_dit(T *input, size_t ntt_len, bool bit_rev = true)
                {
                    ntt_len = max_2pow(ntt_len);
                    if (ntt_len <= 1 || ntt_len > MAX_LEN)
                    {
                        return;
                    }
                    if (ntt_len == 2)
                    {
                        ntt_basic::ntt_2point(input[0], input[1]);
                        return;
                    }
                    if (bit_rev)
                    {
                        binary_reverse_swap(input, ntt_len);
                    }
                    for (size_t pos = 0; pos < ntt_len; pos += 2)
                    {
                        ntt_basic::ntt_2point(input[pos], input[pos + 1]);
                    }
                    for (size_t rank = 2; rank < ntt_len / 2; rank *= 2)
                    {
                        size_t gap = rank * 2;
                        T unit_omega = qpow(T(ROOT), (MOD - 1) / gap);
                        for (size_t begin = 0; begin < ntt_len; begin += (gap * 2))
                        {
                            ntt_basic::ntt_2point(input[begin], input[begin + rank]);
                            ntt_basic::ntt_2point(input[begin + gap], input[begin + rank + gap]);
                            T omega = unit_omega;
                            for (size_t pos = begin + 1; pos < begin + rank; pos++)
                            {
                                ntt_basic::ntt_radix2_dit_butterfly(omega, input + pos, rank);
                                ntt_basic::ntt_radix2_dit_butterfly(omega, input + pos + gap, rank);
                                omega = omega * unit_omega;
                            }
                        }
                    }
                    T omega = 1, unit_omega = qpow(T(ROOT), (MOD - 1) / ntt_len);
                    ntt_len /= 2;
                    for (size_t pos = 0; pos < ntt_len; pos++)
                    {
                        ntt_basic::ntt_radix2_dit_butterfly(omega, input + pos, ntt_len);
                        omega = omega * unit_omega;
                    }
                }
                // 基2频率抽取ntt,学习用
                template <typename T>
                static void ntt_radix2_dif(T *input, size_t ntt_len, bool bit_rev = true)
                {
                    ntt_len = max_2pow(ntt_len);
                    if (ntt_len <= 1 || ntt_len > MAX_LEN)
                    {
                        return;
                    }
                    if (ntt_len == 2)
                    {
                        ntt_basic::ntt_2point(input[0], input[1]);
                        return;
                    }
                    T unit_omega = qpow(T(ROOT), (MOD - 1) / ntt_len);
                    T omega = 1;
                    for (size_t pos = 0; pos < ntt_len / 2; pos++)
                    {
                        ntt_basic::ntt_radix2_dif_butterfly(omega, input + pos, ntt_len / 2);
                        omega = omega * unit_omega;
                    }
                    unit_omega = unit_omega * unit_omega;
                    for (size_t rank = ntt_len / 4; rank > 1; rank /= 2)
                    {
                        size_t gap = rank * 2;
                        for (size_t begin = 0; begin < ntt_len; begin += (gap * 2))
                        {
                            ntt_basic::ntt_2point(input[begin], input[begin + rank]);
                            ntt_basic::ntt_2point(input[begin + gap], input[begin + rank + gap]);
                            T omega = unit_omega;
                            for (size_t pos = begin + 1; pos < begin + rank; pos++)
                            {
                                ntt_basic::ntt_radix2_dif_butterfly(omega, input + pos, rank);
                                ntt_basic::ntt_radix2_dif_butterfly(omega, input + pos + gap, rank);
                                omega = omega * unit_omega;
                            }
                        }
                        unit_omega = unit_omega * unit_omega;
                    }
                    for (size_t pos = 0; pos < ntt_len; pos += 2)
                    {
                        ntt_basic::ntt_2point(input[pos], input[pos + 1]);
                    }
                    if (bit_rev)
                    {
                        binary_reverse_swap(input, ntt_len);
                    }
                }
                template <typename T>
                static constexpr void ntt_split_radix_dit(T input[], size_t ntt_len)
                {
                    NTT_ALT<MAX_LEN, MOD, ROOT>::ntt_dit_template(input, ntt_len);
                }
                template <typename T>
                static constexpr void ntt_split_radix_dif(T input[], size_t ntt_len)
                {
                    NTT_ALT<MAX_LEN, MOD, ROOT>::ntt_dif_template(input, ntt_len);
                }
                template <typename T>
                static constexpr void ntt_dit(T input[], size_t ntt_len)
                {
                    ntt_split_radix_dit(input, ntt_len);
                }
                template <typename T>
                static constexpr void ntt_dif(T input[], size_t ntt_len)
                {
                    ntt_split_radix_dif(input, ntt_len);
                }
                using intt = NTT<mod(), iroot(), MAX_LEN>;
            };
            using ntt1 = NTT<NTT_MOD1, NTT_ROOT1, size_t(1) << 30>;
            using intt1 = ntt1::intt;

            using ntt2 = NTT<NTT_MOD2, NTT_ROOT2, size_t(1) << 28>;
            using intt2 = ntt2::intt;

            using ntt3 = NTT<NTT_MOD3, NTT_ROOT3, size_t(1) << 43>;
            using intt3 = ntt3::intt;

            using ntt4 = NTT<NTT_MOD4, NTT_ROOT4, size_t(1) << 43>;
            using intt4 = ntt4::intt;
        }
        using namespace hint_fft;
        using namespace hint_fht;
        using namespace hint_ntt;
    }
    template <typename T>
    constexpr void normal_convolution(const T in1[], const T in2[], T out[],
                                      size_t len1, size_t len2)
    {
        ary_clr(out, len1 + len2 - 1);
        for (size_t i = 0; i < len1; i++)
        {
            T num1 = in1[i];
            for (size_t j = 0; j < len2; j++)
            {
                out[i + j] = num1 * in2[j];
            }
        }
    }
    inline void fft_convolution(Complex fft_ary1[], Complex fft_ary2[], Complex out[], size_t fft_len)
    {
        hint_transform::fft_dif(fft_ary1, fft_len, false);
        if (fft_ary1 != fft_ary2)
        {
            hint_transform::fft_dif(fft_ary2, fft_len, false);
        }
        HintFloat inv = 1.0 / fft_len;
        for (size_t i = 0; i < fft_len; i++)
        {
            out[i] = std::conj(fft_ary1[i] * fft_ary2[i]) * inv;
        }
        hint_transform::fft_dit(out, fft_len, false);
        for (size_t i = 0; i < fft_len; i++)
        {
            out[i] = std::conj(out[i]);
        }
    }
    void fht_convolution(HintFloat fht_ary1[], HintFloat fht_ary2[], HintFloat out[], size_t fht_len)
    {
        hint_transform::fht(fht_ary1, fht_len);
        if (fht_ary1 != fht_ary2)
        {
            hint_transform::fht(fht_ary2, fht_len);
        }
        out[0] = fht_ary1[0] * fht_ary2[0];
        for (size_t i = 1; i < fht_len; ++i)
        {
            HintFloat tmp1 = fht_ary1[i], tmp2 = fht_ary1[fht_len - i];
            out[i] = (fht_ary2[i] * (tmp1 + tmp2) + fht_ary2[fht_len - i] * (tmp1 - tmp2)) / 2;
        }
        hint_transform::ifht(out, fht_len);
    }
    // 保存数字到数组
    template <UINT_64 BASE, typename T>
    constexpr void save_num_to_ary(T ary[], UINT_64 num, size_t digit)
    {
        size_t i = digit;
        while (i > 0)
        {
            i--;
            ary[i] = num % BASE;
            num /= BASE;
        }
    }
    std::string ui64to_string(UINT_64 input, UINT_8 digits)
    {
        std::string result(digits, '0');
        for (UINT_8 i = 0; i < digits; i++)
        {
            result[digits - i - 1] = static_cast<char>(input % 10 + '0');
            input /= 10;
        }
        return result;
    }
    UINT_64 stoui64(const std::string::const_iterator &begin,
                    const std::string::const_iterator &end, const UINT_32 base = 10)
    {
        UINT_64 result = 0;
        for (auto it = begin; it < end && it - begin < 19; ++it)
        {
            result *= base;
            char c = tolower(*it);
            UINT_64 n = 0;
            if (isalnum(c))
            {
                if (isalpha(c))
                {
                    n = c - 'a' + 10;
                }
                else
                {
                    n = c - '0';
                }
            }
            if (n < base)
            {
                result += n;
            }
        }
        return result;
    }
    UINT_64 stoui64(const std::string &str, const UINT_32 base = 10)
    {
        return stoui64(str.begin(), str.end(), base);
    }

    template <typename T = UINT_32, typename SIZE_TYPE = UINT_32>
    class HintVector
    {
    private:
        T *ary_ptr = nullptr;
        SIZE_TYPE sign_n_len = 0;
        SIZE_TYPE size = 0;
        static constexpr SIZE_TYPE SIZE_TYPE_BITS = sizeof(SIZE_TYPE) * 8;   // size和len成员的比特数
        static constexpr SIZE_TYPE SIZE_80 = (1ull << (SIZE_TYPE_BITS - 1)); // 第一位为1，其余位为0
        static constexpr SIZE_TYPE LEN_MAX = SIZE_80 - 1;                    // 定义最大长度

    public:
        ~HintVector()
        {
            if (ary_ptr != nullptr)
            {
                delete[] ary_ptr;
                ary_ptr = nullptr;
            }
        }
        HintVector()
        {
            ary_ptr = nullptr;
        }
        HintVector(SIZE_TYPE ele_size)
        {
            if (ele_size > 0)
            {
                resize(ele_size);
            }
        }
        HintVector(SIZE_TYPE ele_size, T ele)
        {
            if (ele_size > 0)
            {
                resize(ele_size);
                change_length(ele_size);
                fill_element(ele, ele_size);
            }
        }
        HintVector(const T *ary, SIZE_TYPE len)
        {
            if (ary == nullptr)
            {
                throw("Can't copy from nullptr\n");
            }
            if (len > 0)
            {
                resize(len);
                change_length(len);
                ary_copy(ary_ptr, ary, len);
            }
        }
        HintVector(const HintVector &input)
        {
            if (input.ary_ptr != nullptr)
            {
                if (ary_ptr != nullptr)
                {
                    delete[] ary_ptr;
                }
                ary_ptr = nullptr;
                size_t len = input.length();
                resize(len);
                change_length(len);
                change_sign(input.sign());
                ary_copy(ary_ptr, input.ary_ptr, len);
            }
        }
        HintVector(HintVector &&input)
        {
            if (input.ary_ptr != nullptr)
            {
                size = input.size;
                change_length(input.length());
                change_sign(input.sign());
                if (ary_ptr != nullptr)
                {
                    delete[] ary_ptr;
                }
                ary_ptr = input.ary_ptr;
                input.ary_ptr = nullptr;
            }
        }
        HintVector &operator=(const HintVector &input)
        {
            if (this != &input)
            {
                if (ary_ptr != nullptr)
                {
                    delete[] ary_ptr;
                }
                ary_ptr = nullptr;
                size_t len = input.length();
                resize(len);
                change_length(len);
                change_sign(input.sign());
                ary_copy(ary_ptr, input.ary_ptr, len);
            }
            return *this;
        }
        HintVector &operator=(HintVector &&input)
        {
            if (this != &input)
            {
                size = input.size;
                change_length(input.length());
                change_sign(input.sign());
                if (ary_ptr != nullptr)
                {
                    delete[] ary_ptr;
                }
                ary_ptr = input.ary_ptr;
                input.ary_ptr = nullptr;
            }
            return *this;
        }
        template <typename Ty, typename SIZE_Ty>
        void copy_from(const HintVector<Ty, SIZE_Ty> &input)
        {
            if (this != &input)
            {
                if (input.length() > LEN_MAX)
                {
                    std::cerr << "HintVector err: too long\n";
                    exit(EXIT_FAILURE);
                }
                delete[] ary_ptr;
                ary_ptr = nullptr;
                SIZE_TYPE len = input.length();
                resize(len);
                change_length(len);
                change_sign(input.sign());
                ary_copy_2type(ary_ptr, input.raw_ptr(), len);
            }
        }
        template <typename Ty>
        void copy_from(const Ty *input, SIZE_TYPE len)
        {
            if (input == nullptr)
            {
                throw("Can't copy from nullptr\n");
            }
            len = min(len, length());
            ary_copy(ary_ptr, input, len);
        }
        T front() const
        {
            if (length() == 0)
            {
                return 0;
            }
            return ary_ptr[0];
        }
        T back() const
        {
            if (length() == 0)
            {
                return 0;
            }
            return ary_ptr[length() - 1];
        }
        T &operator[](SIZE_TYPE index) const
        {
            return ary_ptr[index];
        }
        void *raw_ptr() const
        {
            if (ary_ptr == nullptr)
            {
                std::cerr << "HintVector err: Get a ptr from an empty vector\n";
                exit(EXIT_FAILURE);
            }
            return ary_ptr;
        }
        constexpr T *data() const
        {
            return ary_ptr;
        }
        static SIZE_TYPE size_generator(SIZE_TYPE new_size)
        {
            new_size = std::min<SIZE_TYPE>(new_size, LEN_MAX);
            if (new_size <= 2)
            {
                return 2;
            }
            else if (new_size <= 4)
            {
                return 4;
            }
            SIZE_TYPE size1 = min_2pow(new_size);
            SIZE_TYPE size2 = size1 / 2;
            size2 = size2 + size2 / 2;
            if (new_size <= size2)
            {
                return size2;
            }
            else
            {
                return size1;
            }
        }
        void print() const
        {
            SIZE_TYPE i = length();
            if (i == 0 || ary_ptr == nullptr)
            {
                std::cout << "Empty vector" << std::endl;
            }
            while (i > 0)
            {
                i--;
                std::cout << ary_ptr[i] << "\t";
            }
            std::cout << std::endl;
        }
        constexpr SIZE_TYPE capacity() const
        {
            return size;
        }
        constexpr SIZE_TYPE length() const
        {
            return sign_n_len & LEN_MAX;
        }
        bool sign() const
        {
            return (SIZE_80 & sign_n_len) != 0;
        }
        constexpr void resize(SIZE_TYPE new_size, SIZE_TYPE(size_func)(SIZE_TYPE) = size_generator)
        {
            new_size = size_func(new_size);
            if (ary_ptr == nullptr)
            {
                size = new_size;
                ary_ptr = new T[size];
                change_length(0);
            }
            else if (size != new_size)
            {
                size = new_size;
                ary_ptr = ary_realloc(ary_ptr, size);
                change_length(length());
            }
        }
        void change_length(SIZE_TYPE new_length)
        {
            if (new_length > LEN_MAX)
            {
                throw("Length too long\n");
            }
            new_length = std::min(new_length, size);
            bool sign_tmp = sign();
            sign_n_len = new_length;
            change_sign(sign_tmp);
        }
        void change_sign(bool is_sign)
        {
            if ((!is_sign) || length() == 0)
            {
                sign_n_len = sign_n_len & LEN_MAX;
            }
            else
            {
                sign_n_len = sign_n_len | SIZE_80;
            }
        }
        SIZE_TYPE set_true_len()
        {
            if (ary_ptr == nullptr)
            {
                return 0;
            }
            SIZE_TYPE t_len = length();
            while (t_len > 0 && ary_ptr[t_len - 1] == 0)
            {
                t_len--;
            }
            change_length(t_len);
            return length();
        }
        void fill_element(T ele, SIZE_TYPE count, SIZE_TYPE begin = 0)
        {
            if (begin >= size || ary_ptr == nullptr)
            {
                return;
            }
            if (begin + count >= size)
            {
                count = size - begin;
            }
            std::fill(ary_ptr + begin, ary_ptr + begin + count, ele);
        }
        void clear()
        {
            ary_clr(ary_ptr, size);
        }
    };
    template <typename T, typename SIZE_TYPE>
    constexpr SIZE_TYPE HintVector<T, SIZE_TYPE>::SIZE_TYPE_BITS;
    template <typename T, typename SIZE_TYPE>
    constexpr SIZE_TYPE HintVector<T, SIZE_TYPE>::SIZE_80;
    template <typename T, typename SIZE_TYPE>
    constexpr SIZE_TYPE HintVector<T, SIZE_TYPE>::LEN_MAX;
}
#endif