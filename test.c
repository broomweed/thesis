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
    int e = 4;
    /* This is bad but I don't have an
     * annotated version of malloc yet! */
    int* @owned a = (int *@owned) &e;
    int* @owned b = (int *@owned) &e;
    /* This line correctly fails, because
     * we haven't dealt with b yet. */
    b = a;
    return *a;
}
