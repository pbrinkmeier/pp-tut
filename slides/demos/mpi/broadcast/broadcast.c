#include <stdio.h>
#include <mpi.h>

int main(int argc, char** args) {
	int rank, msg;

	MPI_Init(&argc, &args);
	MPI_Comm_rank(MPI_COMM_WORLD, &rank);

	if (rank == 0) {
		msg = 777;
	}

	printf("[%d, before Bcast]: msg = %d\n", rank, msg);
	MPI_Bcast(&msg, 1, MPI_INT, 0, MPI_COMM_WORLD);
	// Barrier is not actually needed but increases output readability
	MPI_Barrier(MPI_COMM_WORLD);
	printf("[%d, after Bcast ]: msg = %d\n", rank, msg);

	MPI_Finalize();

	return 0;
}
