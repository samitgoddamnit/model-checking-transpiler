#include <stdlib.h>

void safe(int n)
{
    int *x = malloc(sizeof(int));

    if (n > 0)
    {
        free(x);
    }
    else
    {
        free(x);
    }
}

int main(void)
{
    safe(5);
    return 0;
}