#include "hint_mini.hpp"
#include <chrono>

void test_mul()
{
    using namespace hint;
    size_t len = 100;
    Integer a = std::string(len, '9');
    Integer b = std::string(len, '7');
    a = "46583359999494021748720564947744";
    b = "94265163159445991488";
    auto t1 = std::chrono::high_resolution_clock::now();
    // a *= b;
    auto t2 = std::chrono::high_resolution_clock::now();
    a %= b;
    auto t3 = std::chrono::high_resolution_clock::now();
    std::cout << std::string(a) << std::endl;
    std::cout << std::chrono::duration_cast<std::chrono::microseconds>(t2 - t1).count() << "us\n";
}

void test_inv()
{
    using namespace hint;
    using Span = Integer::Span;
    size_t len = 1e5;
    std::vector<uint16_t> v(len), inv(len + 1), r(len * 2 + 1);
    r[len * 2] = 1;
    for (size_t i = 0; i < len; ++i)
    {
        v[i] = (i + 1) % 10000;
    }
    v.back() = 5000;
    auto t1 = std::chrono::high_resolution_clock::now();
    Integer::absInvNewton(Span(v.data(), v.size()), Span(inv.data(), inv.size()));
    auto t2 = std::chrono::high_resolution_clock::now();
    Integer a = Span(inv.data(), inv.size());
    Integer b = Span(r.data(), r.size());
    Integer c = Span(v.data(), v.size());
    std::cout << b << std::endl;
    std::cout << c << std::endl;
    auto t3 = std::chrono::high_resolution_clock::now();
    c = a * c;
    auto t4 = std::chrono::high_resolution_clock::now();
    // std::cout << a - b << std::endl;
    std::cout << std::chrono::duration_cast<std::chrono::microseconds>(t2 - t1).count() << "us\n";
    std::cout << std::chrono::duration_cast<std::chrono::microseconds>(t4 - t3).count() << "us\n";
}

#include <random>
void test_div()
{
    using namespace hint;
    size_t len = 1000000;
    std::string s1(len * 2, '9'), s2(len, '7');
    for (size_t i = 0; i < len; ++i)
    {
        s1[i] = rand() % 10 + '0';
        s2[i] = rand() % 10 + '0';
    }
    Integer a = s1, b = s2;
    auto t1 = std::chrono::high_resolution_clock::now();
    Integer q = a / b;
    auto t2 = std::chrono::high_resolution_clock::now();
    Integer r = a % b;
    auto t3 = std::chrono::high_resolution_clock::now();
    Integer prod = q * b;
    auto t4 = std::chrono::high_resolution_clock::now();
    if (b < 0)
    {
        assert(r <= 0 && r > b);
    }
    else
    {
        assert(r >= 0 && r < b);
    }
    std::cout << "Quotient: " << q << std::endl;
    std::cout << "Remainder: " << r << std::endl;
    assert(a == prod + r);
    std::cout << "Div: " << std::chrono::duration_cast<std::chrono::microseconds>(t2 - t1).count() << "us\n";
    std::cout << "Mod: " << std::chrono::duration_cast<std::chrono::microseconds>(t3 - t2).count() << "us\n";
    std::cout << "Mul: " << std::chrono::duration_cast<std::chrono::microseconds>(t4 - t3).count() << "us\n";
}

int main()
{
    // test_mul();
    // test_inv();
    test_div();
}