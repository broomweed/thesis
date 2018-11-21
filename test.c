typedef struct schmoo {
    int yes;
} schmoo;

typedef schmoo* blorp;

typedef schmoo bloop;

const int x;

int blah(const int y) {
    blorp @owned z;
    bloop* x;
    int e = 4;
    /* This is bad but I don't have an
     * annotated version of malloc yet! */
    int* @owned a = (int *@owned) &e;
    int* @owned b = (int *@owned) &e;

    /* This fails (correctly!) because
     * we haven't dealt with b yet.
     * Adding "@owned" to c's type signature
     * makes the test pass! */
    int* c = b;
    b = a;

    return *b;
}
