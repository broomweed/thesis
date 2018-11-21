int main() {
    int *@owned a;
    int *@owned b;
    int q = 2;

    if (q > 0) {
        a = (int *@owned) malloc(sizeof(int));
    } else {
        a = (int *@owned) malloc(sizeof(int));
        b = (int *@owned) malloc(sizeof(int));
    }

    b = a;

    free(b);

    return 0;
}
