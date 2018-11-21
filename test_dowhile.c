int main(int argc, char **argv) {
    int *@owned c;
    int *@owned d = (int *@owned) malloc(4);

    int i = 8;

    do {
        c = (int *@owned)malloc(4); // simulated malloc
        i--;
        free(d);
        d = c;
    } while (i > 0);

    c = d;

    return 0;
}
