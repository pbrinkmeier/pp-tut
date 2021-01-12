#include <stdio.h>
#include <mpi.h>

void custom_Bcast(void *buf, int count, MPI_Datatype type, int root, MPI_Comm comm) {
	int unique_tag = 42;
        // TODO
}

int main(int argc, char** args) {
	int rank, msg;

	MPI_Init(&argc, &args);
	MPI_Comm_rank(MPI_COMM_WORLD, &rank);

        msg = rank;

	printf("[%d, before Bcast]: msg = %d\n", rank, msg);
	custom_Bcast(&msg, 1, MPI_INT, 0, MPI_COMM_WORLD);
	// Barrier is not actually needed but increases output readability
	MPI_Barrier(MPI_COMM_WORLD);
	printf("[%d, after Bcast ]: msg = %d\n", rank, msg);

	MPI_Finalize();

	return 0;
}
