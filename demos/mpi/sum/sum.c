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

    if (rank == 0) {
        for (int i = 0; i < x * size; i++) {
            all_xs[i] = i + 1;
        }
        printf("Initialized %d elements\n", x * size);
    }

    // TODO: Verteile an jeden Prozess jeweils x Elemente (in all_xs)

    printf("First element in %d: %ld\n", rank, all_xs[0]);

    long local_sum = 0;
    for (int i = 0; i < x; i++) {
        local_sum += all_xs[i];
    }

    long sums[size];
    // TODO: Sammle alle local_sum im Array sums

    long sum;
    // TODO: Summiere alle Einträge von sums in sum

    if (rank == 0) {
        printf("Total: %ld\n", sum);
    }

	MPI_Finalize();

	return 0;
}
