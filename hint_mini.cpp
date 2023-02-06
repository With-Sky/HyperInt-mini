#include <iostream>
#include "hint_mini.hpp"
#include "stopwatch.hpp"

using namespace std;
int main()
{
    StopWatch w(1000);
    size_t len = 10000000;
    int n = 1;
    // cin >> len;
    Integer a = string(len, '9');
    Integer b = string(len, '7');
    w.start();
    a = a * b;
    // try
    // {
    //     std::cout << div_test(a, b) << "\n";
    // }
    // catch (const char *e)
    // {
    //     std::cerr << e << '\n';
    // }
    w.stop();
    cout << a << "\n";
    // cout << a.length() << "\n";
    cout << w.duration() << "ms\n";
    // cin.get();
}