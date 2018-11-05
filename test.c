typedef struct schmoo {
    int yes;
} schmoo;

typedef schmoo* const blorp;

typedef schmoo bloop;

const int x;

int blah(const int y) {
    blorp z;
    return z->yes;
}
