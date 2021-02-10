void testcase1() {
    int cachePower = 16; // cache size = 2^16B
    int blockPower = 5; // block size = 2^5B
    int stride = 1;
    int N = 1024;
    long[] A = new long[N];
    String cacheType = "FullyAssociative";

    for (int i = 0;i < N;i+=1){
        A[i] = 0;
    }
}
void testcase2() {
    int cachePower = 16; // cache size = 2^16B
    int blockPower = 5; // block size = 2^5B
    int N = 256;
    int[][] Z = new int[N][N];
    String cacheType = "FullyAssociative";
    for (int i = 0; i < N; i += 1) {
        for (int j = 0; j < N; j += 1) {
            Z[i][j] = 0;
        }
    }
}

void testcase3() {
    int cachePower = 18; // cache size = 2^18B
    int blockPower = 6; // block size = 2^6B
    int N = 256;
    int[][] A = new int[N][N];
    int[][] B = new int[N][N];
    int[][] C = new int[N][N];
    String cacheType = "FullyAssociative";
    for (int i = 0; i < N; i += 1) {
        for (int j = 0; j < N; j += 1) {
            int sum = 0;
            for (int k = 0; k < N; k += 1) {
                sum += A[i][k] * B[k][j];
            }
            C[i][j] = sum;
        }
    }
}


