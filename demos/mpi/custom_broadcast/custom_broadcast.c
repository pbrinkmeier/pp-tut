#include <stdio.h>
#include <mpi.h>

void custom_Bcast(void *buf, int count, MPI_Datatype type, int root, MPI_Comm comm) {
    /* Könnt ihr so lassen :) */
	int unique_tag = 100;

    int rank;
	MPI_Comm_rank(comm, &rank);
	int size;
	MPI_Comm_size(comm, &size);

	if (rank == root) {
		for (int i = 0; i < size; i++) {
			if (i != root) {
				MPI_Send(buf, count, type, i, unique_tag, comm);
			}
		}
	} else {
		MPI_Recv(buf, count, type, root, unique_tag, comm, NULL);
	}
}

int main(int argc, char** args) {
	int rank, msg;

	MPI_Init(&argc, &args);
	MPI_Comm_rank(MPI_COMM_WORLD, &rank);

    msg = rank;

	printf("[%d, before Bcast]: msg = %d\n", rank, msg);
	custom_Bcast(&msg, 1, MPI_INT, 0, MPI_COMM_WORLD);
	// MPI_Bcast(&msg, 1, MPI_INT, 0, MPI_COMM_WORLD);
	// Barrier brauchen wir nicht unbedingt, macht aber die Ausgabe schöner
    fflush(stdout);
	MPI_Barrier(MPI_COMM_WORLD);
	printf("[%d, after Bcast ]: msg = %d\n", rank, msg);
	// In der Ausgabe sollte für jeden Prozess i stehen:
	// [i, after Bcast]: msg = 0

	MPI_Finalize();

	return 0;
}
