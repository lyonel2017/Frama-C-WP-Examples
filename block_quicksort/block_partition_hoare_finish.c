#define BLOCKSIZE 3

static inline int block_partition_hoare_finish(int *arr, int begin, int end)
{
    int last = end - 1;
    int mid = begin + ((end - begin) / 2);
    unsigned char indexL[BLOCKSIZE], indexR[BLOCKSIZE];
    if (less(arr[mid], arr[begin]))
    {
        if (less(arr[last], arr[begin]))
        {
            if (less(arr[mid], arr[last]))
            {
                swap(arr[begin], arr[last]);
            }
            else
            {
                int temp = arr[mid];
                arr[mid] = arr[last];
                arr[last] = arr[begin];
                arr[begin] = arr[temp];
            }
        }
    }
    else
    { // mid > begin
        if (less(arr[last], arr[begin]))
        { // mid > begin > last
            swap(arr[mid], arr[last]);
        }
        else
        {
            if (arr[mid] < arr[last])
            { // begin < mid < last
                swap(arr[begin], arr[mid]);
            }
            else
            { // begin < mid, mid > last
                int temp = arr[mid];
                arr[mid] = arr[begin];
                arr[begin] = arr[last];
                arr[last] = temp;
            }
        }
    }

    int q = arr[begin];
    mid = begin++;
    int temp;
    last--;
    int iL = 0;
    int iR = 0;
    int sL = 0;
    int sR = 0;
    int j;
    int num;
    while (last - begin + 1 > 2 * BLOCKSIZE)
    {
        if (iL == 0)
        {
            sL = 0;
            for (j = 0; j < BLOCKSIZE; j++)
            {
                indexL[iL] = j;
                iL += !(arr[begin + j] < q);
            }
        }
        if (iR == 0)
        {
            sR = 0;
            for (j = 0; j < BLOCKSIZE; j++)
            {
                indexR[iR] = j;
                iR += !(q < arr[last - j]);
            }
        }
        num = min(iL, iR);
        if (num != 0)
        {
            temp = arr[begin + indexL[sL]];
            arr[begin + indexL[sL]] = arr[last - indexR[sR]];
            for (j = 1; j < num; j++)
            {
                arr[last - indexR[sR + j - 1]] = arr[begin + indexL[sL + j]];
                arr[begin + indexL[sL + j]] = arr[last - indexR[sR + j]];
            }
            arr[last - indexR[sR + num - 1]] = temp;
        }
        iL -= num;
        iR -= num;
        sL += num;
        sR += num;
        if (iL == 0)
            begin += BLOCKSIZE;
        if (iR == 0)
            last -= BLOCKSIZE;
    }
    begin--;
    last++;
loop:
    do
        ;
    while (arr[++begin] < q);
    do
        ;
    while (q < arr[--last]);
    if (begin <= last)
    {
        swap(arr[begin], arr[last]);
        goto loop;
    }
    swap(arr[mid], arr[last]);
    return last;
}

