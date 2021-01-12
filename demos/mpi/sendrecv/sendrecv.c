#include <stdio.h>
#include <mpi.h>

#define TAG 42

int main(int argc, char** args) {
	int size;
	int rank;

	MPI_Init(&argc, &args);
	MPI_Comm_size(MPI_COMM_WORLD, &size);
	MPI_Comm_rank(MPI_COMM_WORLD, &rank);

	int msg = 1;
	
	MPI_Status status;
	if (rank != 0) {
		MPI_Recv(&msg, 1, MPI_INT, rank - 1, TAG, MPI_COMM_WORLD, &status);
		printf("I, %d, have received message %d\n", rank, msg);
	}

	if (rank != size - 1) {
		msg = msg * 2;
		MPI_Send(&msg, 1, MPI_INT, rank + 1, TAG, MPI_COMM_WORLD);
		printf("I, %d, have sent message %d to %d\n", rank, msg, rank + 1);
	}

	MPI_Finalize();

	return 0;
}
