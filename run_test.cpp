/* Copyright 2009, 2010 Brendan Tauras */

/* run_test.cpp is part of FlashSim. */

/* FlashSim is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * any later version. */

/* FlashSim is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details. */

/* You should have received a copy of the GNU General Public License
 * along with FlashSim.  If not, see <http://www.gnu.org/licenses/>. */

/****************************************************************************/

/* Basic test driver
 * Brendan Tauras 2009-11-02
 *
 * driver to create and run a very basic test of writes then reads */

#include "ssd.h"
#include <stdlib.h>
#define SIZE 3000

using namespace ssd;

int main()
{
	load_config();
	print_config(NULL);
   //printf("Press ENTER to continue...");
   //getchar();
   printf("\n");

	Ssd *ssd = new Ssd();

	double result = 0;

//	// Test one write to some blocks.
//	for (int i = 0; i < SIZE; i++)
//	{
//		/* event_arrive(event_type, logical_address, size, start_time) */
//		result = ssd -> event_arrive(WRITE, i*100000, 1, (double) 1+(250*i));
//
//		printf("Write time: %.20lf\n", result);
////		result = ssd -> event_arrive(WRITE, i+10240, 1, (double) 1);
////
//	}
//	for (int i = 0; i < SIZE; i++)
//	{
//		/* event_arrive(event_type, logical_address, size, start_time) */
//		result = ssd -> event_arrive(READ, i*100000, 1, (double) 1+(500*i));
//		printf("Read time : %.20lf\n", result);
////		result = ssd -> event_arrive(READ, i, 1, (double) 1);
////		printf("Read time : %.20lf\n", result);
//	}

//	// Test writes and read to same block.
//	for (int i = 0; i < SIZE; i++)
//	{
//		result = ssd -> event_arrive(WRITE, i%64, 1, (double) 1+(250*i));
//
//		printf("Write time: %.20lf\n", result);
//	}
//	for (int i = 0; i < SIZE; i++)
//	{
//		result = ssd -> event_arrive(READ, i%64, 1, (double) 1+(500*i));
//		printf("Read time : %.20lf\n", result);
//	}

	// Test random writes to a block
	// result = ssd -> event_arrive(WRITE, 5, 1, (double) 0.0);
	// printf("Write time: %.20lf\n", result);
	// result = ssd -> event_arrive(WRITE, 5, 1, (double) 200.0);
	// printf("Write time: %.20lf\n", result);
	// result = ssd -> event_arrive(WRITE, 5, 1, (double) 600.0);
	// printf("Write time: %.20lf\n", result);
	// result = ssd -> event_arrive(WRITE, 2, 1, (double) 900.0);
	// printf("Write time: %.20lf\n", result);
	// result = ssd -> event_arrive(WRITE, 1, 1, (double) 1200.0);
	// printf("Write time: %.20lf\n", result);
	// result = ssd -> event_arrive(WRITE, 5, 1, (double) 1500.0);
	// printf("Write time: %.20lf\n", result);

	// for (int i = 0; i < SIZE-6; i++)
	// {
	// 	/* event_arrive(event_type, logical_address, size, start_time) */
	// 	result = ssd -> event_arrive(WRITE, 6+i, 1, (double) 1800+(300*i));
	// 	printf("Write time: %.20lf\n", result);
	// }

	// // Force Merge
	// result = ssd -> event_arrive(WRITE, 10 , 1, (double) 0.0);
	// printf("Write time: %.20lf\n", result);
//	for (int i = 0; i < SIZE; i++)
//	{
//		/* event_arrive(event_type, logical_address, size, start_time) */
//		result = ssd -> event_arrive(READ, i%64, 1, (double) 1+(500*i));
//		printf("Read time : %.20lf\n", result);
//	}
	// for (int i = 0; i < SIZE; i++) {
	// 	srand(i);
	// 	printf("<<event %d>> ", i);
	// 	ulong lpn = rand() % 128;

	// 	result += ssd -> event_arrive(WRITE, lpn, 1, (double)100*i);
	// }
	// printf("total write time: %.20lf\n", result);
	// result = 0;
	// for (int i = 0; i < 128; i++) {
	// 	result += ssd -> event_arrive(READ, i, 1, (double)100*i);
	// }
	// printf("total read time: %.20lf\n", result);
	int time = 0;
	for (int i = 1; i <= SIZE; i++) {
		for (int j = 1; j <= 16; j++) {
			if (i >= j && i % j == 0) {
				for(int k = 1; k <= 32; k++) {
				//printf("time: %f /", (double)100*time);
				result += ssd -> event_arrive(WRITE, j*k, 1, (double)100*time++);
				}
			}
		}
	}
	printf("total write time: %.20lf\n", result);
	result = 0;
	time = 0;
	for(int j = 1; j <= 16; j++) {
		for(int k = 1; k <= 32; k++) {
			result += ssd -> event_arrive(READ, j*k, 1, (double)100*time++);
		}
	}
	printf("total read time: %.20lf\n", result);

	delete ssd;
	return 0;
}
