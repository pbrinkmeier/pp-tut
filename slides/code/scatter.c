int nums[4];
int local;
if (rank == 0) { nums = {0, 1, 2, 3}; }

MPI_Scatter(nums, 1, MPI_INT, &local, 1, MPI_INT,
    0, MPI_COMM_WORLD);
// in P_i gilt: local = i
MPI_Gather(&local, 1, MPI_INT, nums, 1, MPI_INT,
    0, MPI_COMM_WORLD);
