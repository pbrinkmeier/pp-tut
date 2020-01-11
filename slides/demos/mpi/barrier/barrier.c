#include <stdio.h>
#include <mpi.h>

int main(int argc, char** args) {
	int size;
	int rank;

	MPI_Init(&argc, &args);
	MPI_Comm_size(MPI_COMM_WORLD, &size);
	MPI_Comm_rank(MPI_COMM_WORLD, &rank);
	
	for (int i = 0; i < 3; i++) {
		MPI_Barrier(MPI_COMM_WORLD);
		printf("[%d] says: i = %d\n", rank, i);
	}

	MPI_Finalize();

	return 0;
}
