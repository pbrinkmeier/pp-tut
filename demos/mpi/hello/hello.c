#include <stdio.h>
#include <mpi.h>

void task(long n) {
  long sum = 0;
  for (long i = 0; i < n; i++) {
    sum++;
  }
  printf("Sum: %ld\n", sum);
}

int main(int argc, char** args) {
	int size;
	int rank;
int processor_name_length;

	MPI_Init(&argc, &args);
	MPI_Comm_size(MPI_COMM_WORLD, &size);
	MPI_Comm_rank(MPI_COMM_WORLD, &rank);

	printf("Hello world, I have rank %d out of %d\n", rank, size);
        long N = 10000000000;
        task(N / size);

	MPI_Finalize();

	return 0;
}
