#include <stdio.h>
#include <stdlib.h>
#include <mpi.h>

#define x 1000

int main(int argc, char** args) {
	int size;
	int rank;

	MPI_Init(&argc, &args);
	MPI_Comm_size(MPI_COMM_WORLD, &size);
	MPI_Comm_rank(MPI_COMM_WORLD, &rank);

    long all_xs[x * size];
    long sums[size];

    if (rank == 0) {
        for (int i = 0; i < x * size; i++) {
            all_xs[i] = i + 1;
        }
        printf("Initialized %d elements\n", x * size);
    }

    MPI_Scatter(all_xs, x, MPI_LONG, all_xs, x, MPI_LONG, 0, MPI_COMM_WORLD);

    printf("First element in %d: %ld\n", rank, all_xs[0]);

    long local_sum = 0;
    for (int i = 0; i < x; i++) {
        local_sum += all_xs[i];
    }

    long sum;
    MPI_Reduce(&local_sum, &sum, 1, MPI_LONG, MPI_SUM, 0, MPI_COMM_WORLD);

    if (rank == 0) {
        printf("Total: %ld\n", sum);
    }

	MPI_Finalize();

	return 0;
}
