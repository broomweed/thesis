int main() {
    int *@owned x;// = (int *@owned)malloc(2);
    int i = 8;

    while (i > 0) {
        i--;
        free(x);
        x = (int*@owned)malloc(2);
    }

    int *@owned a = x;
    return 2;
}
