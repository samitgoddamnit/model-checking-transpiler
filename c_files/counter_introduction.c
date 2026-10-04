#include <stdlib.h>

void foo(int n)
{
    int *x = malloc(sizeof(int));

    if (n > 0)
    {
        free(x);
    }

    if (n <= 0)
    {
        free(x);
    }
    bar();
    return;
}

void bar(void)
{
    int *y = malloc(sizeof(int));
    int *s = malloc(sizeof(int));
    int *z = malloc(sizeof(int));
    return;
}

int main(void)
{
    foo(5);
    return 0;
}