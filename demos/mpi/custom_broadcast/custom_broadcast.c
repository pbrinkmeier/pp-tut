#include <stdio.h>
#include <mpi.h>

void custom_Bcast(void *buf, int count, MPI_Datatype type, int root, MPI_Comm comm) {
	int unique_tag = 42;

        int rank, size;
        MPI_Comm_rank(MPI_COMM_WORLD, &rank);
        MPI_Comm_size(MPI_COMM_WORLD, &size);

        if (rank == root) {
                for (int dest = 0; dest < size; dest++) {
                        if (dest != root) {
                                MPI_Send(buf, count, type, dest, unique_tag, comm);
                        }
                }
        } else {
                MPI_Status status;
                MPI_Recv(buf, count, type, root, unique_tag, comm, &status);
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
	// Barrier is not actually needed but increases output readability
        fflush(stdout);
	MPI_Barrier(MPI_COMM_WORLD);
	printf("[%d, after Bcast ]: msg = %d\n", rank, msg);

	MPI_Finalize();

	return 0;
}
