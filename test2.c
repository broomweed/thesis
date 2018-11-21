int main(int argc, char **argv) {
    int *@owned c;
    int *@owned d;

    int i = 8;

    do {
        c = (int *@owned)malloc(hi); // simulated malloc
        i--;
        d = c;
        free(c);
    } while (i > 0);

    return 0;
}
