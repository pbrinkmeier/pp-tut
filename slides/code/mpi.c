#include <mpi.h>

int main(int argc, char** args) {
  int size, rank;

  MPI_Init(&argc, &args);
  MPI_Comm_size(MPI_COMM_WORLD, &size);
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);

  ...

  MPI_Finalize();
}
