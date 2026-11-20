// Compile with the directory containing the pinned 025 closure_check.cpp on the include path.
#define main closure_program_main
#include "closure_check.cpp"
#undef main

int main() {
    CAP = 28;
    CONJ = 7;
    NOSYM = false;
    const std::string logged = "xyxYXY|xxxxYYY";
    const auto start = keyOfSpec(logged);
    for (const char* spec : {"xyxYXY|xxxYYYY", "xxxYYYY|xyxYXY", "YXYxyx|YYYxxxx", "xyxYXY|xxxxYYY"}) {
        const auto key = keyOfSpec(spec);
        std::printf("%s -> %s\n", spec, keyStr(key).c_str());
        if (key != start || keyStr(key) != logged) return 1;
    }
    const auto target = keyOfSpec("x|y");
    std::printf("x|y -> %s\n", keyStr(target).c_str());
    return (target == start || keyStr(target) != "x|y") ? 1 : 0;
}
