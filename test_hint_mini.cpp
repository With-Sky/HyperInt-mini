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
void test_div(size_t len, float k)
{
    using namespace hint;
    std::cout << "Length:" << len << " k:" << k << std::endl;
    std::string s1(len * k, '9'), s2(len, '7');
    srand(0);
    for (auto &c : s1)
    {
        c = rand() % 10 + '0';
    }
    for (auto &c : s2)
    {
        c = rand() % 10 + '0';
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
    assert(a == prod + r);
    // std::cout <<"Quotient:" << q << std::endl;
    // std::cout <<"Remainder:" << r << std::endl;
    std::cout << "Div:" << std::chrono::duration_cast<std::chrono::microseconds>(t2 - t1).count() << "us\n";
    std::cout << "Mod:" << std::chrono::duration_cast<std::chrono::microseconds>(t3 - t2).count() << "us\n";
    std::cout << "Mul:" << std::chrono::duration_cast<std::chrono::microseconds>(t4 - t3).count() << "us\n";
    std::cout << "--------------------------------------------------------------------------------------\n";
}
void test_div_all()
{
    test_div(1e3, 0.9);
    test_div(2e3, 0.9);
    test_div(5e3, 0.9);
    test_div(1e4, 0.9);
    test_div(1e5, 0.9);
    test_div(2e5, 0.9);
    test_div(5e5, 0.9);
    test_div(1e6, 0.9);

    test_div(1e3, 1.01);
    test_div(2e3, 1.01);
    test_div(5e3, 1.01);
    test_div(1e4, 1.01);
    test_div(1e5, 1.01);
    test_div(2e5, 1.01);
    test_div(5e5, 1.01);
    test_div(1e6, 1.01);

    test_div(1e3, 1.02);
    test_div(2e3, 1.02);
    test_div(5e3, 1.02);
    test_div(1e4, 1.02);
    test_div(1e5, 1.02);
    test_div(2e5, 1.02);
    test_div(5e5, 1.02);
    test_div(1e6, 1.02);

    test_div(1e3, 1.4);
    test_div(2e3, 1.4);
    test_div(5e3, 1.4);
    test_div(1e4, 1.4);
    test_div(1e5, 1.4);
    test_div(2e5, 1.4);
    test_div(5e5, 1.4);
    test_div(1e6, 1.4);

    test_div(1e3, 1.5);
    test_div(2e3, 1.5);
    test_div(5e3, 1.5);
    test_div(1e4, 1.5);
    test_div(1e5, 1.5);
    test_div(2e5, 1.5);
    test_div(5e5, 1.5);
    test_div(1e6, 1.5);

    test_div(1e3, 2.0);
    test_div(2e3, 2.0);
    test_div(5e3, 2.0);
    test_div(1e4, 2.0);
    test_div(1e5, 2.0);
    test_div(2e5, 2.0);
    test_div(5e5, 2.0);
    test_div(1e6, 2.0);

    test_div(1e3, 5);
    test_div(2e3, 5);
    test_div(5e3, 5);
    test_div(1e4, 5);
    test_div(1e5, 5);
    test_div(2e5, 5);
    test_div(5e5, 5);
    test_div(1e6, 5);

    test_div(1e3, 10);
    test_div(2e3, 10);
    test_div(5e3, 10);
    test_div(1e4, 10);
    test_div(1e5, 10);
    test_div(2e5, 10);
    test_div(5e5, 10);
    test_div(1e6, 10);
}
void test_fib()
{
    using namespace hint;
    auto t1 = std::chrono::high_resolution_clock::now();
    Integer a = fib2(100000000);
    auto t2 = std::chrono::high_resolution_clock::now();
    std::cout << a << std::endl;
    std::cout << std::chrono::duration_cast<std::chrono::microseconds>(t2 - t1).count() << "us\n";
}

void div_str(const std::string &s1, const std::string &s2)
{
    hint::Integer a = s1, b = s2;
    auto q = a / b;
    auto r = a % b;
    auto prod = q * b;
    std::cout << "q: " << q << std::endl;
    std::cout << "r: " << r << std::endl;
    if (b < 0)
    {
        assert(r <= 0 && r > b);
    }
    else
    {
        assert(r >= 0 && r < b);
    }
    assert(a == prod + r);
}

void test_div_str()
{
    div_str("78956280120995889940283644187011081529620816345643213303605", "7894797141528365916699815572551941661773547");
    div_str("68531229432102693399511930722022626964490095705713208969499031614", "685227870287240733251");
    div_str("7136536140517299", "71357498");
    div_str("4887201181946", "48864");
    div_str("8997512465127264013", "89964615971");
    div_str("6417226261819799685", "641632521412603");
    div_str("67598293602980262493", "6759110519054328");
    div_str("8395653085539", "83948");
    div_str("90484077200794", "9047165549");
    div_str("90421703377908", "9040669327");
    div_str("9857173763", "244146003");
    div_str("8031505449", "122079749");
    div_str("32302792763301767499", "97656515695019687");
    div_str("447327016209964951", "976565871");
    div_str("32329411505963797", "9765684728711");
    div_str("65473856407750249", "976565836");
    div_str("3486539733497304111", "244149359");
    div_str("3530650012292719307", "1220704124367");
    div_str("798418423953", "976565451");
    div_str("95104723841702", "1220704798129");
    div_str("861580423620394069399079918799859841668175090856703557", "976564420738452749803450086210131586793301181");
    div_str("57067629428271558702752690917469225974961105666271788041314490", "4882854694507863679514955994199754473850064136253");
}
int main()
{
    // test_mul();
    // test_inv();
    // test_div_all();
    // test_fib();
    test_div_str();
    return 0;
}
