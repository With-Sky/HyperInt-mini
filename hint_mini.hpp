#include "hint_math.hpp"

#ifndef HINT_MINI_HPP
#define HINT_MINI_HPP
namespace hint_arithm
{
    using namespace hint;
    using SIZE_TYPE = UINT_32;
    template <typename T>
    using hintvector = HintVector<T, SIZE_TYPE>;

    template <typename T>
    void ary_print(T ary[], size_t len)
    {
        size_t i = len;
        while (i > 0)
        {
            i--;
            std::cout << ary[i] << "\t";
        }
        std::cout << "\n";
    }
    // 按位与
    template <typename T>
    constexpr void ary_and(const T in1[], const T in2[], T out[], size_t len1, size_t len2)
    {
        size_t len = std::min(len1, len2);
        size_t mod4 = len % 4;
        len -= mod4;
        for (size_t i = 0; i < len; i += 4)
        {
            out[i] = in1[i] & in2[i];
            out[i + 1] = in1[i + 1] & in2[i + 1];
            out[i + 2] = in1[i + 2] & in2[i + 2];
            out[i + 3] = in1[i + 3] & in2[i + 3];
        }
        for (size_t i = len; i < len + mod4; i++)
        {
            out[i] = in1[i] & in2[i];
        }
    }
    // 按位或
    template <typename T>
    constexpr void ary_or(const T in1[], const T in2[], T out[], size_t len1, size_t len2)
    {
        if (len1 < len2)
        {
            std::swap(in1, in2);
            std::swap(len1, len2);
        }
        size_t mod4 = len2 % 4;
        len2 -= mod4;
        for (size_t i = 0; i < len2; i++)
        {
            out[i] = in1[i] | in2[i];
            out[i + 1] = in1[i + 1] | in2[i + 1];
            out[i + 2] = in1[i + 2] | in2[i + 2];
            out[i + 3] = in1[i + 3] | in2[i + 3];
        }
        for (size_t i = len2; i < len2 + mod4; i++)
        {
            out[i] = in1[i] | in2[i];
        }
        len2 += mod4;
        ary_copy(out + len2, in1 + len2, len1 - len2);
    }
    // 按位异或
    template <typename T>
    constexpr void ary_xor(const T in1[], const T in2[], T out[], size_t len1, size_t len2)
    {
        if (len1 < len2)
        {
            std::swap(in1, in2);
            std::swap(len1, len2);
        }
        size_t mod4 = len2 % 4;
        len2 -= mod4;
        for (size_t i = 0; i < len2; i++)
        {
            out[i] = in1[i] ^ in2[i];
            out[i + 1] = in1[i + 1] ^ in2[i + 1];
            out[i + 2] = in1[i + 2] ^ in2[i + 2];
            out[i + 3] = in1[i + 3] ^ in2[i + 3];
        }
        for (size_t i = len2; i < len2 + mod4; i++)
        {
            out[i] = in1[i] ^ in2[i];
        }
        len2 += mod4;
        ary_copy(out + len2, in1 + len2, len1 - len2);
    }
    // 按位取反
    template <typename T>
    constexpr void ary_not(const T in[], T out[], size_t len)
    {
        size_t mod4 = len % 4;
        len -= mod4;
        for (size_t i = 0; i < len; i += 4)
        {
            out[i] = ~in[i];
            out[i + 1] = ~in[i + 1];
            out[i + 2] = ~in[i + 2];
            out[i + 3] = ~in[i + 3];
        }
        for (size_t i = len; i < len + mod4; i++)
        {
            out[i] = ~in[i];
        }
    }
    // 数组整体右移
    template <typename T>
    constexpr void ary_rshift(const T in[], T out[], size_t len)
    {
        size_t mod4 = len % 4;
        len -= mod4;
        for (size_t i = 0; i < len; i += 4)
        {
            out[i] = ~in[i];
            out[i + 1] = ~in[i + 1];
            out[i + 2] = ~in[i + 2];
            out[i + 3] = ~in[i + 3];
        }
        for (size_t i = len; i < len + mod4; i++)
        {
            out[i] = ~in[i];
        }
    }
    // 数组整体左移
    template <typename T>
    constexpr void ary_lshift(const T in[], T out[], size_t len)
    {
        size_t mod4 = len % 4;
        len -= mod4;
        for (size_t i = 0; i < len; i += 4)
        {
            out[i] = ~in[i];
            out[i + 1] = ~in[i + 1];
            out[i + 2] = ~in[i + 2];
            out[i + 3] = ~in[i + 3];
        }
        for (size_t i = len; i < len + mod4; i++)
        {
            out[i] = ~in[i];
        }
    }
    // 高精度绝对值比较,前者大于后者返回1,小于返回-1等于返回0
    template <typename T>
    constexpr INT_32 abs_compare(const T ary1[], const T ary2[], size_t len1, size_t len2)
    {
        len1 = ary_true_len(ary1, len1);
        len2 = ary_true_len(ary2, len2);
        if (len1 != len2)
        {
            return len1 > len2 ? 1 : -1;
        }
        if (ary1 == ary2)
        {
            return 0;
        }
        while (len1 > 0)
        {
            len1--;
            T num1 = ary1[len1], num2 = ary2[len1];
            if (num1 != num2)
            {
                return num1 > num2 ? 1 : -1;
            }
        }
        return 0;
    }
    // 与左移后的ary2绝对值比较,前者大于后者返回1,小于返回-1等于返回0
    template <typename T>
    constexpr INT_32 abs_compare_shift(const T ary1[], const T ary2[], size_t len1, size_t len2, size_t shift = 0)
    {
        len1 = ary_true_len(ary1, len1);
        len2 = ary_true_len(ary2, len2);
        if (len1 != len2 + shift)
        {
            return len1 > (len2 + shift) ? 1 : -1;
        }
        INT_32 cmp = abs_compare(ary1 + shift, ary2, len1, len2);
        if (cmp != 0)
        {
            return cmp;
        }
        for (size_t i = 0; i < shift; i++)
        {
            if (ary1[i] > 0)
            {
                return 1;
            }
        }
        return 0;
    }
    // 高精度加法
    template <bool is_carry = true, typename T>
    constexpr void abs_add(const T in1[], const T in2[], T out[],
                           size_t len1, size_t len2, const UINT_64 base)
    {
        if (len1 < len2)
        {
            std::swap(in1, in2);
            std::swap(len1, len2);
        }
        size_t pos = 0;
        UINT_64 carry = 0;
        while (pos < len2)
        {
            carry += (in1[pos] + in2[pos]);
            out[pos] = carry < base ? carry : carry - base;
            carry = carry < base ? 0 : 1;
            pos++;
        }
        while (pos < len1 && carry > 0)
        {
            carry += in1[pos];
            out[pos] = carry < base ? carry : carry - base;
            carry = carry < base ? 0 : 1;
            pos++;
        }
        ary_copy(out + pos, in1 + pos, len1 - pos);
        if (is_carry)
        {
            out[len1] = carry % base;
        }
    }
    // 高精度减法
    template <typename T>
    constexpr void abs_sub(const T in1[], const T in2[], T out[],
                           size_t len1, size_t len2, const INT_64 base)
    {
        if (len1 < len2)
        {
            return;
        }
        size_t pos = 0;
        INT_64 borrow = 0;
        while (pos < len2)
        {
            borrow += (static_cast<INT_64>(in1[pos]) - in2[pos]);
            out[pos] = borrow < 0 ? borrow + base : borrow;
            borrow = borrow < 0 ? -1 : 0;
            pos++;
        }
        while (pos < len1 && borrow < 0)
        {
            borrow += in1[pos];
            out[pos] = borrow < 0 ? borrow + base : borrow;
            borrow = borrow < 0 ? -1 : 0;
            pos++;
        }
        ary_copy(out + pos, in1 + pos, len1 - pos);
    }
    // 64位搞精度加法
    constexpr void abs_add64(const UINT_64 in1[], const UINT_64 in2[], UINT_64 out[],
                             size_t len1, size_t len2)
    {
        if (len1 < len2)
        {
            std::swap(in1, in2);
            std::swap(len1, len2);
        }
        size_t pos = 0;
        UINT_64 carry = 0;
        while (pos < len2)
        {
            bool is_carry1 = false, is_carry2 = false;
            std::tie(carry, is_carry1) = safe_add(carry, in1[pos]);
            std::tie(carry, is_carry2) = safe_add(carry, in2[pos]);
            out[pos] = carry;
            carry = is_carry1 || is_carry2 ? 1 : 0;
            pos++;
        }
        while (pos < len1)
        {
            bool is_carry = false;
            std::tie(carry, is_carry) = safe_add(carry, in1[pos]);
            out[pos] = carry;
            carry = carry ? 1 : 0;
            pos++;
        }
        out[len1] = carry;
    }
    // 64位多精度减法
    constexpr void abs_sub64(const UINT_64 in1[], const UINT_64 in2[], UINT_64 out[],
                             size_t len1, size_t len2)
    {
        if (len1 < len2)
        {
            std::swap(in1, in2);
            std::swap(len1, len2);
        }
        size_t pos = 0;
        UINT_64 carry = 0;
        while (pos < len2)
        {
            bool is_carry1 = false, is_carry2 = false;
            std::tie(carry, is_carry1) = safe_add(carry, in1[pos]);
            std::tie(carry, is_carry2) = safe_add(carry, in2[pos]);
            out[pos] = carry;
            carry = is_carry1 || is_carry2 ? 1 : 0;
            pos++;
        }
        while (pos < len1)
        {
            bool is_carry = false;
            std::tie(carry, is_carry) = safe_add(carry, in1[pos]);
            out[pos] = carry;
            carry = carry ? 1 : 0;
            pos++;
        }
        out[len1] = carry;
    }
    // 小学乘法
    template <typename T>
    void normal_mul(const T in1[], const T in2[], T out[],
                    size_t len1, size_t len2, const UINT_64 base)
    {
        if (len1 < len2)
        {
            std::swap(in1, in2);
            std::swap(len1, len2);
        }
        if (len1 == 0 || in1 == nullptr || in2 == nullptr)
        {
            return;
        }
        T *res = out;
        if (in1 == out || in2 == out)
        {
            res = new T[len1 + len2];
        }
        ary_clr(res, len1 + len2);
        for (size_t i = 0; i < len1; i++)
        {
            UINT_64 num1 = in1[i];
            for (size_t j = 0; j < len2; j++)
            {
                UINT_64 tmp = num1 * in2[j];
                for (size_t k = i + j; tmp > 0 && k < len1 + len2; k++)
                {
                    tmp += res[k];
                    std::tie(tmp, res[k]) = div_mod(tmp, base);
                }
            }
        }
        if (res != out)
        {
            ary_copy(out, res, len1 + len2);
            delete[] res;
        }
    }
    // fft加速乘法
    template <typename T>
    void fft_mul(const T in1[], const T in2[], T out[],
                 size_t len1, size_t len2, const UINT_64 base)
    {
        if (len1 == 0 || len2 == 0 || in1 == nullptr || in2 == nullptr)
        {
            return;
        }
        size_t conv_res_len = len1 + len2 - 1;   // 卷积结果长度
        size_t fft_len = min_2pow(conv_res_len); // fft长度
        Complex *fft_ary = new Complex[fft_len];
        com_ary_combine_copy(fft_ary, in1, len1, in2, len2);
        hint_transform::fft_dif(fft_ary, fft_len, false);
        for (size_t i = 0; i < fft_len; i++)
        {
            Complex tmp = fft_ary[i];
            fft_ary[i] = std::conj(tmp * tmp);
        }
        hint_transform::fft_dit(fft_ary, fft_len, false);
        hint::UINT_64 carry = 0;
        double inv = 2 * fft_len;
        for (size_t i = 0; i < conv_res_len; i++)
        {
            carry += static_cast<hint::UINT_64>(-fft_ary[i].imag() / inv + 0.5);
            std::tie(carry, out[i]) = div_mod<UINT_64>(carry, base);
        }
        out[conv_res_len] = carry % base;
        delete[] fft_ary;
    }
    // fht加速乘法
    template <typename T>
    void fht_sqr(const T in[], T out[], size_t len, const UINT_64 base)
    {
        if (len == 0 || in == nullptr)
        {
            return;
        }
        size_t conv_res_len = len * 2 - 1;       // 卷积结果长度
        size_t fht_len = min_2pow(conv_res_len); // fht长度
        double *fht_ary = new double[fht_len * 2];
        ary_clr(fht_ary, fht_len);
        ary_copy_2type(fht_ary, in, len);
        fht_convolution(fht_ary, fht_ary, fht_ary + fht_len, fht_len);
        hint::UINT_64 carry = 0;
        for (size_t i = 0; i < conv_res_len; i++)
        {
            carry += static_cast<hint::UINT_64>(fht_ary[i + fht_len] + 0.5);
            std::tie(carry, out[i]) = div_mod(carry, base);
        }
        out[conv_res_len] = carry % base;
        delete[] fht_ary;
    }
    // ntt加速乘法
    template <typename T>
    void ntt_mul(const T in1[], const T in2[], T out[],
                 size_t len1, size_t len2, const UINT_64 base)
    {
        if (len1 == 0 || len2 == 0 || in1 == nullptr || in2 == nullptr)
        {
            return;
        }
        size_t conv_res_len = len1 + len2 - 1;   // 卷积结果长度
        size_t ntt_len = min_2pow(conv_res_len); // ntt长度
        UINT_32 *ntt_ary1 = new UINT_32[ntt_len * 4];
        ary_clr(ntt_ary1, ntt_len * 4);
        UINT_32 *ntt_ary2 = ntt_ary1 + ntt_len;
        UINT_32 *ntt_ary3 = ntt_ary1 + ntt_len * 2;
        UINT_32 *ntt_ary4 = ntt_ary1 + ntt_len * 3;
        hint::ary_copy_2type(ntt_ary1, in1, len1);
        hint::ary_copy_2type(ntt_ary2, in1, len1);
        hint::ary_copy_2type(ntt_ary3, in2, len2);
        hint::ary_copy_2type(ntt_ary4, in2, len2);

        constexpr UINT_64 mod1 = NTT_MOD1, mod2 = NTT_MOD2;
        constexpr UINT_64 root1 = NTT_ROOT1, root2 = NTT_ROOT2;

        hint_transform::ntt<mod1, root1>(ntt_ary1, ntt_len);
        hint_transform::ntt<mod2, root2>(ntt_ary2, ntt_len);
        hint_transform::ntt<mod1, root1>(ntt_ary3, ntt_len);
        hint_transform::ntt<mod2, root2>(ntt_ary4, ntt_len);
        hint::ary_mul_mod<mod1>(ntt_ary1, ntt_ary3, ntt_ary1, ntt_len);
        hint::ary_mul_mod<mod2>(ntt_ary2, ntt_ary4, ntt_ary2, ntt_len);
        hint_transform::intt<mod1, root1>(ntt_ary1, ntt_len);
        hint_transform::intt<mod2, root2>(ntt_ary2, ntt_len);

        hint::UINT_64 carry = 0;
        for (size_t i = 0; i < conv_res_len; i++)
        {
            carry += qcrt<mod1, mod2>(ntt_ary1[i], ntt_ary2[i]);
            std::tie(carry, out[i]) = div_mod(carry, base);
        }
        out[conv_res_len] = carry % base;
        delete[] ntt_ary1;
    }
    // ntt加速平方
    template <typename T>
    void ntt_sqr(const T in[], T out[], size_t len, const UINT_64 base)
    {
        if (len == 0 || in == nullptr)
        {
            return;
        }
        size_t conv_res_len = len * 2 - 1;       // 卷积结果长度
        size_t ntt_len = min_2pow(conv_res_len); // ntt长度
        UINT_32 *ntt_ary1 = new UINT_32[ntt_len * 2];
        ary_clr(ntt_ary1, ntt_len * 2);
        UINT_32 *ntt_ary2 = ntt_ary1 + ntt_len;
        hint::ary_copy_2type(ntt_ary1, in, len);
        hint::ary_copy(ntt_ary2, ntt_ary1, len);

        constexpr UINT_64 mod1 = NTT_MOD1, mod2 = NTT_MOD2;
        constexpr UINT_64 root1 = NTT_ROOT1, root2 = NTT_ROOT2;

        hint_transform::ntt<mod1, root1>(ntt_ary1, ntt_len);
        hint_transform::ntt<mod2, root2>(ntt_ary2, ntt_len);

        hint::ary_mul_mod<mod1>(ntt_ary1, ntt_ary1, ntt_ary1, ntt_len);
        hint::ary_mul_mod<mod2>(ntt_ary2, ntt_ary2, ntt_ary2, ntt_len);

        hint_transform::intt<mod1, root1>(ntt_ary1, ntt_len);
        hint_transform::intt<mod2, root2>(ntt_ary2, ntt_len);

        hint::UINT_64 carry = 0;
        for (size_t i = 0; i < conv_res_len; i++)
        {
            carry += qcrt<mod1, mod2>(ntt_ary1[i], ntt_ary2[i]);
            std::tie(carry, out[i]) = div_mod(carry, base);
        }
        out[conv_res_len] = carry % base;
        delete[] ntt_ary1;
    }
    // karatsuba乘法
    template <typename T, typename NTT_Ty = UINT_16>
    constexpr void karatsuba_mul(const T in1[], const T in2[], T out[],
                                 size_t len1, size_t len2, const INT_64 base)
    {
        // (a*base^n+b)*(c*base^n+d) = a*c*base^2n+(a*d+b*c)*base^n+b*d
        // compute: a*c,b*d,(a+b)*(c+d),a*b+b*c = (a+b)*(c+d)-a*c-b*d
        len1 = ary_true_len(in1, len1);
        len2 = ary_true_len(in2, len2);
        if (len1 < len2)
        {
            std::swap(in1, in2);
            std::swap(len1, len2);
        }
        // std::cin.get();
        if (len2 == 0 || in1 == nullptr || in2 == nullptr)
        {
            return;
        }
        if (len1 + len2 - 1 <= NTT_MAX_LEN)
        {
            const size_t ntt_len1 = len1 * std::max<size_t>(1, sizeof(T) / sizeof(NTT_Ty));
            const size_t ntt_len2 = len2 * std::max<size_t>(1, sizeof(T) / sizeof(NTT_Ty));
            if (in1 == in2 && len1 == len2)
            {
                ntt_sqr<NTT_Ty>(in1, out, ntt_len1, base);
            }
            else
            {
                ntt_mul<NTT_Ty>(in1, in2, out, ntt_len1, ntt_len2, base);
            }
            return;
        }
        size_t len_a = len1 / 2;
        size_t len_b = len1 - len_a; // 公共长度
        size_t len_c = len2 > len_b ? len2 - len_b : 1;
        size_t len_d = len2 > len_b ? len_b : len2;

        size_t len_ac = len_c > 0 ? len_a + len_c : 0; // a*c的长度
        size_t len_bd = len_b + len_d;                 // b*d的长度
        size_t len_add_mul = len_b + len_d + 2;        //(a+b)*(c*d)的长度

        const T *a_ptr = in1 + len_b; // in1代表b
        const T *c_ptr = in2 + len_d; // in2代表d

        hintvector<T> mul_ac(len_ac, 0);       // 存储a*c
        hintvector<T> mul_bd(len_bd, 0);       // 存储b*d
        hintvector<T> add_mul(len_add_mul, 0); // 存储a+b与c+d,a+b的长度为len_b+1

        T *add_ab = add_mul.type_ptr();
        T *add_cd = add_ab + len_b + 1;

        abs_add(in1, a_ptr, add_ab, len_b, len_a, base); // b+a
        abs_add(in2, c_ptr, add_cd, len_d, len_c, base); // d+c

        size_t len_add_ab = ary_true_len(add_ab, len_b + 1);
        size_t len_add_cd = ary_true_len(add_cd, len_d + 1);

        karatsuba_mul(a_ptr, c_ptr, mul_ac.type_ptr(), len_a, len_c, base);            // a*c
        karatsuba_mul(in1, in2, mul_bd.type_ptr(), len_b, len_d, base);                // b*d
        karatsuba_mul(add_ab, add_cd, add_mul.type_ptr(), len_b + 1, len_d + 1, base); //(a+b)*(c+d)
        add_mul.change_length(len_add_ab + len_add_cd);

        len_ac = mul_ac.set_true_len();
        len_bd = mul_bd.set_true_len();
        len_add_mul = add_mul.set_true_len();

        ary_clr(out, len1 + len2);
        ary_copy(out, mul_bd.type_ptr(), len_bd); // 结果加上b*d
        ary_copy(out + len_b * 2, mul_ac.type_ptr(), len_ac);

        INT_64 carry = 0;
        for (size_t pos = len_b; pos < len1 + len2; pos++)
        {
            size_t t_pos = pos - len_b;
            carry += out[pos];
            if (t_pos < len_add_mul)
            {
                carry += add_mul[t_pos];
            }
            if (t_pos < len_ac)
            {
                carry -= mul_ac[t_pos];
            }
            if (t_pos < len_bd)
            {
                carry -= mul_bd[t_pos];
            }
            INT_64 rem = carry % base;
            carry = carry < 0 ? (carry + 1) / base - 1 : carry / base;
            out[pos] = rem < 0 ? rem + base : rem;
        }
    }
    // 高精度乘法
    template <typename T>
    constexpr void abs_mul(const T in1[], const T in2[], T out[],
                           size_t len1, size_t len2, const INT_64 base)
    {
        len1 = ary_true_len(in1, len1);
        len2 = ary_true_len(in2, len2);
        // if (len1 + len2 <= 48 || len1 * len2 < (len1 + len2) * std::log2(len1 + len2))
        // {
        //     normal_mul(in1, in2, out, len1, len2, base);
        // }
        // else if (len1 + len2 - 1 <= (1 << hint_transform::lut_max_rank))
        // {
        //     fft_mul(in1, in2, out, len1, len2, base);
        // }
        // else if (len1 + len2 - 1 <= NTT_MAX_LEN)
        {
            ntt_mul(in1, in2, out, len1, len2, base);
        }
        // else
        // {
        //     karatsuba_mul(in1, in2, out, len1, len2, base);
        // }
    }
    // 高精度平方
    template <typename T>
    constexpr void abs_sqr(const T in[], T out[], size_t len, const INT_64 base)
    {
        len = ary_true_len(in, len);
        if (len <= 24)
        {
            normal_mul(in, in, out, len, len, base);
        }
        else if (len * 2 - 1 <= (1 << hint_transform::lut_max_rank))
        {
            fht_sqr(in, out, len, base);
        }
        else if (len * 2 - 1 <= NTT_MAX_LEN)
        {
            ntt_sqr(in, out, len, base);
        }
        else
        {
            karatsuba_mul(in, in, out, len, len, base);
        }
    }
    // 高精度非平衡乘法
    template <typename T>
    constexpr void abs_mul_balance(const T in1[], const T in2[], T out[],
                                   size_t len1, size_t len2, const INT_64 base)
    {
        if (len1 < len2)
        {
            std::swap(in1, in2);
            std::swap(len1, len2);
        }
        size_t count = (len1 + len2 - 1) / len2;
        size_t block_size = len1 / count;
        size_t len = len1 + block_size - count * block_size;
        if (len > 0)
        {
            abs_mul(in1, in2, out, len, len2, base);
        }
        if (len == len1)
        {
            return;
        }
        hintvector<T> prod(block_size + len2);
        size_t mul_len = len + len2;
        while (len < len1)
        {
            abs_mul(in1 + len, in2, prod.type_ptr(), block_size, len2, base);
            abs_add(out + len, prod.type_ptr(), out + len, mul_len - block_size, block_size + len2, base);
            mul_len = block_size + len2;
            len += block_size;
        }
    }
    // 高精度乘低精度
    template <bool is_carry = true, typename T>
    constexpr void abs_mul_num(const T in[], T num, T out[], size_t len, const UINT_64 base)
    {
        len = ary_true_len(in, len);
        num %= base;
        UINT_64 prod = 0;
        if (num == 1)
        {
            ary_copy(out, in, len);
        }
        else
        {
            for (size_t i = 0; i < len; i++)
            {
                prod += static_cast<UINT_64>(in[i]) * num;
                std::tie(prod, out[i]) = div_mod<UINT_64>(prod, base);
            }
        }
        if (is_carry)
        {
            out[len] = prod;
        }
    }

    // 除以num的同时返回余数
    template <typename T>
    constexpr INT_64 abs_div_num(const T in[], T num, T out[], size_t len, const UINT_64 base)
    {
        size_t pos = ary_true_len(in, len);
        num %= base;
        if (num == 1)
        {
            ary_copy(out, in, len);
            return 0;
        }
        UINT_64 last_rem = 0;
        while (pos > 0)
        {
            pos--;
            last_rem = last_rem * base + in[pos];
            std::tie(out[pos], last_rem) = div_mod<UINT_64>(last_rem, num);
        }
        return last_rem;
    }
    // 除数的规则化
    template <typename T>
    constexpr T divisor_normalize(const T in[], T out[], size_t len, const UINT_64 base)
    {
        if (in == out)
        {
            throw("In can't be same as out\n");
        }
        T multiplier = 1;
        if (len == 1)
        {
            multiplier = (base - 1) / in[0];
            out[0] = in[0] * multiplier;
        }
        else if (in[len - 1] >= (base / 2))
        {
            ary_copy(out, in, len);
        }
        else
        {
            multiplier = (base - 1) * base / (base * in[len - 1] + in[len - 2]);
            abs_mul_num<false>(in, multiplier, out, len, base);
            if (out[len - 1] < (base / 2))
            {
                multiplier++;
                abs_add<false>(out, in, out, len, len, base);
            }
        }
        return multiplier;
    }
    // 长除法,从被除数返回余数,需要确保除数的规则化
    template <typename T>
    void abs_long_div(T dividend[], const T divisor[], T quot[],
                      size_t len1, size_t len2, const UINT_64 base)
    {
        len1 = ary_true_len(dividend, len1);
        len2 = ary_true_len(divisor, len2);
        if (divisor == nullptr || len2 == 0)
        {
            throw("Can't divide by zero\n");
        }
        if (dividend == nullptr || len1 == 0)
        {
            return;
        }
        if (abs_compare(dividend, divisor, len1, len2) < 0)
        {
            return;
        }
        if (len2 == 1)
        {
            T rem = abs_div_num(dividend, divisor[0], quot, len1, base);
            dividend[0] = rem;
            return;
        }
        if (divisor[len2 - 1] < (base / 2))
        {
            throw("Can't call this proc before normalize the divisor\n");
        }
        quot[len1 - len2] = 0;
        const UINT_64 divisor_2digits = base * divisor[len2 - 1] + divisor[len2 - 2];

        hintvector<T> sub(len2 + 1);
        sub.change_length(len2 + 1);

        // 被除数(余数大于等于除数则继续减)
        while (abs_compare(dividend, divisor, len1, len2) >= 0)
        {
            sub.change_length(len2 + 1);
            UINT_64 dividend_2digits = dividend[len1 - 1] * base + dividend[len1 - 2];
            T quo_digit = 0;
            size_t shift = len1 - len2;
            // 被除数前两位大于等于除数前两位试商的结果偏差不大于1
            if (dividend_2digits >= divisor_2digits)
            {
                quo_digit = dividend_2digits / divisor_2digits;
                abs_mul_num(divisor, quo_digit, sub.type_ptr(), len2, base);
                sub.set_true_len();
                size_t sub_len = sub.length();
                if (abs_compare(dividend + shift, sub.type_ptr(), len1 - shift, sub_len) < 0)
                {
                    quo_digit--;
                    abs_sub(sub.type_ptr(), divisor, sub.type_ptr(), sub_len, len2, base);
                }
            }
            else
            {
                // 被除数前两位和除数前一位试商的结果偏差不大于2
                quo_digit = dividend_2digits / (divisor_2digits / base);
                if (quo_digit >= base)
                {
                    quo_digit = base - 1;
                }
                shift--;
                abs_mul_num(divisor, quo_digit, sub.type_ptr(), len2, base);
                sub.set_true_len();
                size_t sub_len = sub.length();
                if (abs_compare(dividend + shift, sub.type_ptr(), len1 - shift, sub_len) < 0)
                {
                    quo_digit--;
                    abs_sub(sub.type_ptr(), divisor, sub.type_ptr(), sub_len, len2, base);
                    if (abs_compare(dividend + shift, sub.type_ptr(), len1 - shift, sub_len) < 0)
                    {
                        quo_digit--;
                        abs_sub(sub.type_ptr(), divisor, sub.type_ptr(), sub_len, len2, base);
                    }
                }
            }
            abs_sub(dividend + shift, sub.type_ptr(), dividend + shift, len1, sub.length(), base);
            len1 = ary_true_len(dividend, len1);
            quot[shift] = quo_digit;
        }
    }
    // 递归除法,从被除数返回余数,需要确保除数的规则化
    template <typename T>
    void abs_rec_div(T dividend[], T divisor[], hintvector<T> &quot,
                     size_t len1, size_t len2, const UINT_64 base)
    {
        len1 = ary_true_len(dividend, len1);
        len2 = ary_true_len(divisor, len2);

        if (divisor == nullptr || len2 == 0)
        {
            throw("Can't divide by zero\n");
        }
        if (dividend == nullptr || len1 == 0)
        {
            return;
        }
        if (abs_compare(dividend, divisor, len1, len2) < 0)
        {
            return;
        }
        if (divisor[len2 - 1] < (base / 2))
        {
            throw("Can't call this proc before normalize the divisor\n");
        }
        size_t quot_len = len1 - len2 + 1;
        quot.change_length(quot_len);
        constexpr size_t LONG_DIV_THRESHOLD = 50;
        if (len2 <= LONG_DIV_THRESHOLD) // 小于等于阈值调用长除法
        {
            abs_long_div(dividend, divisor, quot.type_ptr(), len1, len2, base);
        }
        else if (len1 >= len2 * 2 || len1 > ((len2 + 1) / 2) * 3) // 2n/n的除法，进行两次递归
        {
            size_t base_len = (len1 + 3) / 4;
            size_t quot_tmp_len = base_len * 3 - len2 + 2;
            hintvector<T> quot_tmp(quot_tmp_len, 0);

            abs_rec_div(dividend + base_len, divisor, quot_tmp, len1 - base_len, len2, base);
            quot_tmp_len = quot_tmp.set_true_len();
            size_t dividend_len = ary_true_len(dividend, len1);
            abs_rec_div(dividend, divisor, quot, dividend_len, len2, base);
            quot.change_length(quot_len);
            quot_len = quot.set_true_len();
            abs_add(quot.type_ptr() + base_len, quot_tmp.type_ptr(), quot.type_ptr() + base_len, quot_len - base_len, quot_tmp_len, base);
            quot.change_length(len1 - len2 + 1);
        }
        else
        {
            // 开始试商,用dividend/(base^base_len)除以divisor/(base^base_len)
            size_t base_len = len2 / 2;
            abs_rec_div(dividend + base_len, divisor + base_len, quot, len1 - base_len, len2 - base_len, base);

            constexpr T ONE[1] = {1};
            quot_len = quot.set_true_len();
            hintvector<T> prod(base_len + quot_len);
            prod.change_length(base_len + quot_len);
            // 用除数的低base_len位乘以刚刚试出来的商,而后与余数比较,必须满足quot*(divisor%(base^base_len))<=dividend
            abs_mul(divisor, quot.type_ptr(), prod.type_ptr(), base_len, quot_len, base);
            size_t prod_len = prod.set_true_len();
            len1 = ary_true_len(dividend, len1);

            while (abs_compare(prod.type_ptr(), dividend, prod_len, len1) > 0)
            {
                abs_sub(quot.type_ptr(), ONE, quot.type_ptr(), quot_len, 1, base);
                abs_sub(prod.type_ptr(), divisor, prod.type_ptr(), prod_len, base_len, base);
                abs_add(dividend + base_len, divisor + base_len, dividend + base_len, len1 - base_len, len2 - base_len, base);

                quot_len = quot.set_true_len();
                prod_len = prod.set_true_len();
                len1 = ary_true_len(dividend, std::max(len1, len2) + 1);
            }
            abs_sub(dividend, prod.type_ptr(), dividend, len1, prod_len, base);
        }
    }
    // 绝对值除法
    template <typename T>
    hintvector<T> abs_div(const T dividend[], T divisor[], hintvector<T> &quot,
                          size_t len1, size_t len2, const UINT_64 base, bool ret_rem = true)
    {
        hintvector<T> normalized_divisor(len2); // 定义规则化的除数
        normalized_divisor.change_length(len2);
        hintvector<T> normalized_dividend(len1 + 1); // 定义规则化的被除数
        normalized_dividend.change_length(len1 + 1);

        T *divisor_ptr = normalized_divisor.type_ptr();
        T *dividend_ptr = normalized_dividend.type_ptr();
        T multiplier = divisor_normalize(divisor, divisor_ptr, len2, base); // 除数规则化,获得乘数
        abs_mul_num(dividend, multiplier, dividend_ptr, len1, base);        // 被除数规则化
        len1 = normalized_dividend.set_true_len();
        quot = hintvector<T>(len1 - len2 + 2, 0);
        if ((!ret_rem) && (len1 + 2 < len2 * 2))
        {
            // 除数过长时可以截取一部分不参与计算
            size_t shift = len2 * 2 - len1 - 2;
            abs_rec_div(dividend_ptr + shift, divisor_ptr + shift, quot, len1 - shift, len2 - shift, base);
            quot.set_true_len();
            return normalized_dividend;
        }
        abs_rec_div(dividend_ptr, divisor_ptr, quot, len1, len2, base);
        quot.set_true_len();
        if (ret_rem)
        {
            len1 = normalized_dividend.set_true_len();
            abs_div_num(dividend_ptr, multiplier, dividend_ptr, len1, base); // 余数除以乘数得到正确的结果
            normalized_dividend.set_true_len();
        }
        return normalized_dividend;
    }
    /// @brief 高精度进制转换
    /// @tparam T
    /// @tparam UNIT_T
    /// @param data_ary 输入表示大整数的数组,需留有充足空间
    /// @param BASE1 输入进制
    /// @param BASE2 输出进制
    template <typename T>
    void base_conversion(T data_ary[], size_t &in_len,
                         const UINT_64 BASE1 = 1 << 16, const UINT_64 BASE2 = 1e4)
    {
        if (in_len == 0 || BASE1 == BASE2)
        {
            return;
        }
        if (in_len < 2)
        {
            UINT_64 tmp = data_ary[0];
            size_t pos = 0;
            while (tmp > 0)
            {
                std::tie(tmp, data_ary[pos]) = div_mod(tmp, BASE2);
                pos++;
            }
            return;
        }
        const size_t max_rank = min_2pow(in_len) / 2;                                                      // unit_ary存储的base1的最高次幂
        const UINT_64 base1to2_len = static_cast<UINT_64>(std::ceil(std::log2(BASE1) / std::log2(BASE2))); // base1到base2的数长度的比值
        size_t result_len = static_cast<size_t>(max_rank * base1to2_len * 2);                              // 结果的长度

        ary_clr(data_ary + in_len, result_len - in_len); // 清零
        // 输入进制比输出进制大进行预处理
        if (BASE1 > BASE2)
        {
            size_t pos = in_len;
            while (pos > 0)
            {
                pos--;
                UINT_64 tmp = data_ary[pos];
                size_t i = 0, trans_pos = pos * base1to2_len;
                while (tmp > 0)
                {
                    std::tie(tmp, data_ary[trans_pos + i]) = div_mod(tmp, BASE2);
                    i++;
                }
            }
            UINT_64 tmp = BASE2;
            while (tmp < BASE1)
            {
                tmp *= BASE2;
                if (tmp == BASE1)
                {
                    return;
                }
            }
        }
        size_t unit_ary_len = max_rank * base1to2_len; // unit_ary的长度max_rank
        T *unit_ary = new T[unit_ary_len];             // 用一个数组存储base2进制下的(base1)^1,(base1)^2,(base1)^4...
        ary_clr(unit_ary, unit_ary_len);
        UINT_64 tmp = BASE1;
        size_t i = 0;
        while (tmp > 0)
        {
            std::tie(tmp, unit_ary[i]) = div_mod(tmp, BASE2); // 将base2进制下的base1存入数组
        }
        T *tmp_product = new T[max_rank * base1to2_len * 2];
        for (size_t rank = 1; rank <= max_rank; rank *= 2)
        {
            size_t gap = rank * 2;
            for (size_t i = 0; i < result_len; i += gap)
            {
                T *work_ary = data_ary + i;
                abs_mul(work_ary + rank, unit_ary, tmp_product, rank, rank, BASE2);
                abs_add<false>(work_ary, tmp_product, work_ary, rank, gap, BASE2);
            }
            if (rank < max_rank)
            {
                abs_sqr(unit_ary, unit_ary, rank, BASE2);
            }
        }
        result_len = ary_true_len(data_ary, result_len);
        in_len = result_len;
        delete[] unit_ary;
        delete[] tmp_product;
    }
}

// 简单高精度简单实现
class Integer
{
public:
    using DataType = hint::UINT_16;
    using SizeType = hint::UINT_32;
    using DataVec = hint::HintVector<DataType, SizeType>;

private:
    DataVec data;

public:
    static constexpr hint::UINT_32 DIGIT = 4;
    static constexpr hint::UINT_64 BASE = hint::qpow(10, DIGIT);
    Integer()
    {
        data = DataVec();
    }
    // Integer 拷贝构造
    Integer(const Integer &input)
    {
        if (this != &input)
        {
            data = input.data;
        }
    }
    // Integer 移动构造
    Integer(Integer &&input) noexcept
    {
        if (this != &input)
        {
            data = std::move(input.data);
        }
    }
    // string 参数构造
    Integer(const std::string &input)
    {
        string_in(input);
    }
    // 字符串构造
    Integer(char input[])
    {
        string_in(input);
    }
    // 字符串构造
    Integer(const char input[])
    {
        string_in(input);
    }
    // 通用构造
    template <typename T>
    Integer(T input)
    {
        bool is_neg = hint::is_neg(input);
        hint::UINT_64 tmp = std::abs<hint::INT_64>(input);
        size_t digits = std::ceil(std::log10(tmp + 1));
        size_t len = (digits + DIGIT - 1) / DIGIT;
        data = DataVec(len);
        data.change_length(len);
        for (size_t i = 0; i < len; i++)
        {
            data[i] = tmp % BASE;
            tmp /= BASE;
        }
        data.change_sign(is_neg);
        data.set_true_len();
    }
    // Integer 拷贝赋值
    Integer &operator=(const Integer &input)
    {
        if (this != &input)
        {
            data = input.data;
        }
        return *this;
    }
    // Integer 移动赋值
    Integer &operator=(Integer &&input) noexcept
    {
        if (this != &input)
        {
            data = std::move(input.data);
        }
        return *this;
    }
    // string 赋值
    Integer &operator=(const std::string &input)
    {
        string_in(input);
        return *this;
    }
    // 字符串赋值
    Integer &operator=(const char input[])
    {
        string_in(input);
        return *this;
    }
    // 字符串赋值
    Integer &operator=(char input[])
    {
        string_in(input);
        return *this;
    }
    // 通用赋值
    template <typename T>
    Integer &operator=(T input)
    {
        bool is_neg = hint::is_neg(input);
        hint::UINT_64 tmp = std::abs<hint::INT_64>(input);
        size_t digits = std::ceil(std::log10(tmp + 1));
        size_t len = (digits + DIGIT - 1) / DIGIT;
        data = DataVec(len);
        data.change_length(len);
        for (size_t i = 0; i < len; i++)
        {
            std::tie(tmp, data[i]) = hint::div_mod(tmp, BASE);
        }
        data.change_sign(is_neg);
        data.set_true_len();
        return *this;
    }
    // 首位的数字
    DataType first_num() const
    {
        if (length() == 0)
        {
            return 0;
        }
        return data[length() - 1];
    }
    // 前2位的数字
    hint::UINT_64 first2_num() const
    {
        if (length() < 2)
        {
            return first_num();
        }
        return data[length() - 1] * BASE + data[length() - 2];
    }
    // 更改符号
    void change_sign(bool is_neg)
    {
        data.change_sign(is_neg);
    }
    // 是否为负号
    bool is_neg() const
    {
        return data.sign();
    }
    SizeType length() const
    {
        return data.length();
    }
    SizeType length_base10() const
    {
        size_t len = data.length();
        if (len == 0)
        {
            return 1;
        }
        return (len - 1) * DIGIT + std::ceil(std::log10(first_num() + 1));
    }
    void string_in(const std::string &str)
    {
        size_t str_len = str.size();
        if (str_len == 0)
        {
            data = DataVec();
            return;
        }
        hint::INT_64 len = str_len, pos = len, i = 0;
        bool is_neg = false;
        if (str[0] == '-')
        {
            is_neg = true;
            len--;
        }
        len = (len + DIGIT - 1) / DIGIT;
        data = DataVec(len);
        data.change_length(len);
        while (pos - DIGIT > 0)
        {
            hint::UINT_64 tmp = hint::stoui64(str.begin() + pos - DIGIT, str.begin() + pos);
            data[i] = static_cast<DataType>(tmp);
            i++;
            pos -= DIGIT;
        }
        hint::INT_64 begin = is_neg ? 1 : 0;
        if (pos > begin)
        {
            hint::UINT_64 tmp = hint::stoui64(str.begin() + begin, str.begin() + pos);
            data[i] = static_cast<DataType>(tmp);
        }
        change_sign(is_neg);
        data.set_true_len();
    }
    std::string to_string() const
    {
        std::string result;
        size_t pos = length();
        if (pos == 0)
        {
            return "0";
        }
        if (is_neg())
        {
            result += '-';
        }
        result += std::to_string(first_num());
        pos--;
        while (pos > 0)
        {
            pos--;
            result += hint::ui64to_string(data[pos], DIGIT);
        }
        return result;
    }
    void print() const
    {
        size_t pos = length();
        if (pos < 1)
        {
            putchar('0');
            return;
        }
        if (is_neg())
        {
            putchar('-');
        }
        printf("%d", first_num());
        pos--;
        while (pos > 0)
        {
            pos--;
            printf(" %04d", data[pos]);
        }
        putchar('\n');
    }
    friend std::istream &operator>>(std::istream &is, Integer &num)
    {
        std::string tmp;
        is >> tmp;
        num.string_in(tmp);
        return is;
    }
    friend std::ostream &operator<<(std::ostream &os, const Integer &num)
    {
        return os << num.to_string();
    }
    hint::INT_32 abs_compare(const Integer &input) const
    {
        size_t len1 = length(), len2 = input.length();
        return hint_arithm::abs_compare(data.type_ptr(), input.data.type_ptr(), len1, len2);
    }
    Integer abs_add(const Integer &input) const
    {
        size_t len1 = length(), len2 = input.length();
        Integer result;
        result.data = DataVec(std::max(len1, len2) + 1);
        result.data.change_length(std::max(len1, len2) + 1);
        auto ptr1 = data.type_ptr();
        auto ptr2 = input.data.type_ptr();
        auto res_ptr = result.data.type_ptr();
        hint_arithm::abs_add<true>(ptr1, ptr2, res_ptr, len1, len2, BASE);
        result.data.set_true_len();
        return result;
    }
    Integer abs_sub(const Integer &input) const
    {
        size_t len1 = length(), len2 = input.length();
        Integer result;
        result.data = DataVec(std::max(len1, len2));
        result.data.change_length(std::max(len1, len2));
        auto ptr1 = data.type_ptr();
        auto ptr2 = input.data.type_ptr();
        auto res_ptr = result.data.type_ptr();
        hint_arithm::abs_sub(ptr1, ptr2, res_ptr, len1, len2, BASE);
        result.data.set_true_len();
        return result;
    }
    bool operator>(const Integer &input) const
    {
        if (is_neg() != input.is_neg())
        {
            return !is_neg();
        }
        return is_neg() != (abs_compare(input) > 0);
    }
    bool operator<(const Integer &input) const
    {
        if (is_neg() != input.is_neg())
        {
            return is_neg();
        }
        return is_neg() != (abs_compare(input) < 0);
    }
    bool operator>=(const Integer &input) const
    {
        return !(*this < input);
    }
    bool operator<=(const Integer &input) const
    {
        return !(*this > input);
    }
    bool operator==(const Integer &input) const
    {
        if (is_neg() != input.is_neg())
        {
            return false;
        }
        return abs_compare(input) == 0;
    }
    bool operator!=(const Integer &input) const
    {
        return !(*this == input);
    }
    Integer operator+(const Integer &input) const
    {
        Integer result;
        if (is_neg() == input.is_neg()) // 是否同号
        {
            result = abs_add(input);
            result.change_sign(is_neg());
        }
        else
        {
            const hint::INT_32 cmp = abs_compare(input);
            if (cmp > 0)
            {
                result = abs_sub(input);
                result.change_sign(is_neg());
            }
            else if (cmp < 0)
            {
                result = input.abs_sub(*this);
                result.change_sign(!is_neg());
            }
        }
        return result;
    }
    Integer operator-(const Integer &input) const
    {
        Integer result;
        if (this == &input)
        {
            return result;
        }
        if (is_neg() != input.is_neg()) // 是否异号
        {
            result = abs_add(input);
            result.change_sign(is_neg());
        }
        else
        {
            const hint::INT_32 cmp = abs_compare(input);
            if (cmp > 0)
            {
                result = abs_sub(input);
                result.change_sign(is_neg());
            }
            else if (cmp < 0)
            {
                result = input.abs_sub(*this);
                result.change_sign(!is_neg());
            }
        }
        return result;
    }
    Integer operator*(const Integer &input) const
    {
        Integer result;
        size_t len1 = length(), len2 = input.length();
        if (len1 == 0 || len2 == 0)
        {
            return result;
        }
        result.data = DataVec(len1 + len2);
        result.data.change_length(len1 + len2);
        result.data.clear();
        auto ptr1 = data.type_ptr();
        auto ptr2 = input.data.type_ptr();
        auto res_ptr = result.data.type_ptr();
        if (abs_compare(input) == 0)
        {
            hint_arithm::abs_sqr(ptr1, res_ptr, len1, BASE);
        }
        else
        {
            hint_arithm::abs_mul_balance(ptr1, ptr2, res_ptr, len1, len2, BASE);
        }
        result.data.set_true_len();
        result.change_sign(is_neg() != input.is_neg());
        return result;
    }
    Integer operator/(const Integer &input) const
    {
        Integer result;
        size_t len1 = length(), len2 = input.length();
        if (abs_compare(input) < 0)
        {
            return result;
        }
        if (len2 == 0)
        {
            throw("Can't divide by zero\n");
        }
        auto ptr1 = data.type_ptr();
        auto ptr2 = input.data.type_ptr();

        hint_arithm::abs_div(ptr1, ptr2, result.data, len1, len2, BASE, false);

        result.data.set_true_len();
        result.change_sign(is_neg() != input.is_neg());
        return result;
    }
    Integer operator%(const Integer &input) const
    {
        Integer result;
        size_t len1 = length(), len2 = input.length();
        if (abs_compare(input) < 0)
        {
            return *this;
        }
        if (len2 == 0)
        {
            throw("Can't divide by zero\n");
        }
        auto ptr1 = data.type_ptr();
        auto ptr2 = input.data.type_ptr();

        result.data = hint_arithm::abs_div(ptr1, ptr2, result.data, len1, len2, BASE);

        result.data.set_true_len();
        result.change_sign(is_neg() != input.is_neg());
        return result;
    }
};
Integer pi_generator(hint::UINT_32 n)
{
    n += 5;
    Integer result = hint::qpow(Integer(10), n) * Integer(2);
    Integer a = result / 3;
    result = result + a;
    hint::UINT_32 i = 2;
    while (a.length() > 0)
    {
        a = a * i;
        a = a / (i * 2 + 1);
        result = result + a;
        i++;
    }
    return result;
}
template <typename T>
bool div_test(const T &dividend, const T &divisor)
{
    T quo = dividend / divisor;
    T rem = dividend % divisor;
    T prod = quo * divisor;
    bool t1 = (dividend >= prod) && (dividend < (prod + divisor));
    bool t2 = (prod + rem == dividend);
    return t1 && t2;
}
#endif