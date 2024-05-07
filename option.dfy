// source: lemon option.c

module {:extern "Lemon"} Lemon {
    class ConsoleIO {
        method {:extern "ConsoleIO", "WriteLine"} WriteLine(x: string)
    }
}

datatype option_type = OPT_FLAG | OPT_INT | OPT_DBL | OPT_STR | OPT_FFLAG | OPT_FINT | OPT_FDBL | OPT_FSTR
datatype s_options = s_options(s_type: option_type, s_label: string, arg: string, message: string)
class LOption {
    var g_argv: array<string>
    var op: array<s_options>
    var errstream: int

    constructor(argv: array<string>, options: array<s_options>, f: int) {
        g_argv := argv;
        op := options;
        errstream := f;
    }

    predicate Valid()
        reads this
    {
        && g_argv.Length >= 0
        && op.Length >= 0
    }

    function ISOPT(X: string): bool
        requires |X| > 0
    {
        (X[0] == '-'|| X[0] == '+' || '=' in X)
    }


}
