typedef struct schmoo {
    int yes;
} schmoo;

typedef schmoo* blorp;

typedef schmoo bloop;

const int x;

int blah(const int y) {
    blorp @owned z;
    bloop* x;
    x = z;
    z = x;
    return z->yes;
}
