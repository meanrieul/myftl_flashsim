/* Copyright 2011 Matias Bjørling */

/* dftp_ftl.cpp */

/* FlashSim is free software: you can redistribute it and/or modify
* it under the terms of the GNU General Public License as published by
* the Free Software Foundation, either version 3 of the License, or
* any later version. */

/* FlashSim is distributed in the hope that it will be useful,
* but WITHOUT ANY WARRANTY; without even the implied warranty of
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
* GNU General Public License for more details. */

/* You should have received a copy of the GNU General Public License
* along with FlashSim. If not, see <http://www.gnu.org/licenses/>. */

/****************************************************************************/

/* Implementation of the DFTL described in the paper
* "DFTL: A Flasg Translation Layer Employing Demand-based Selective Caching og Page-level Address Mappings"
*
* Global Mapping Table GMT
* Global Translation Directory GTD (Maintained in memory)
* Cached Mapping Table CMT (Uses LRU to pick victim)
*
* Dlpn/Dppn Data Logical/Physical Page Number
* Mlpn/Mppn Translation Logical/Physical Page Number
*
*
* Calculate the AMT by experience
*/


#include <new>
#include <assert.h>
#include <stdio.h>
#include <math.h>
#include <vector>
#include <queue>
#include <iostream>
#include "../ssd.h"

using namespace ssd;

FtlImpl_My1::FtlImpl_My1(Controller &controller):
FtlImpl_DftlParent(controller)
{
	uint ssdSize = NUMBER_OF_ADDRESSABLE_BLOCKS * BLOCK_SIZE;
	AMT_table = new AvgModifiedTime[ssdSize];
	AMT_block = new AvgModifiedBlock[NUMBER_OF_ADDRESSABLE_BLOCKS];
	prev_start_time = 0;
	printf("Total size to map: %uKB\n", ssdSize * PAGE_SIZE / 1024);
	printf("Using myFTL1.\n");
	return;
}

FtlImpl_My1::~FtlImpl_My1(void)
{
	return;
}

enum status FtlImpl_My1::read(Event &event)
{
	printf("read start - ");
	uint dlpn = event.get_logical_address();
	resolve_mapping(event, false);
	MPage current = trans_map[dlpn];
	if (current.ppn == -1)
	{
		event.set_address(Address(0, PAGE));
		event.set_noop(true);
	}
	else
		event.set_address(Address(current.ppn, PAGE));


	controller.stats.numFTLRead++;
	printf("end\n");
	return controller.issue(event);
}

uint FtlImpl_My1::get_similar_data_block(uint lpn)
{
	// 이진 탐색 써봐도 될 듯
	// printf("AMT_table[lpn].timeTaken: %f\n", AMT_table[lpn].timeTaken);
	// int idx = 0;
	// if(AMT_table[lpn].timeTaken == 0) {
	// 	while(AMT_block[idx].pageCount >= BLOCK_SIZE && idx < NUMBER_OF_ADDRESSABLE_BLOCKS - 1) idx++;
	// 	return idx;
	// }

	// int s_idx = 0; // shorter timeTaken BLOCK index
	// int l_idx = 0; // longer timeTaken BLOCK index
	// for(l_idx = 0; l_idx < NUMBER_OF_ADDRESSABLE_BLOCKS; l_idx++) {
	// 	if(AMT_block[l_idx].validCount && AMT_block[l_idx].timeTaken >= AMT_table[lpn].timeTaken) break;
	// }
	// for(s_idx = NUMBER_OF_ADDRESSABLE_BLOCKS - 1; s_idx >= 0; s_idx--) {
	// 	if(AMT_block[s_idx].validCount && AMT_block[s_idx].timeTaken <= AMT_table[lpn].timeTaken) break;
	// }
	// printf("s: %d / l:%d /", s_idx, l_idx);
	// for(idx = s_idx; idx <= l_idx; idx++){
	// 	if(AMT_block[idx].pageCount < BLOCK_SIZE){
	// 		break;
	// 	}
	// }
	// printf("%d\n", idx);
	// return idx;
	double min = 99999999999;
	int min_idx = -1;
	double dist = 0;
	for(int i = 0; i < NUMBER_OF_ADDRESSABLE_BLOCKS; i++){
		if(AMT_block[i].pageCount == BLOCK_SIZE) continue;
		dist = fabs(AMT_block[lpn].timeTaken - AMT_block[i].timeTaken);
		if(dist < min) {
			min = dist;
			min_idx = i;
		}
	}
	return min_idx;
}

// block select and get free data page
long FtlImpl_My1::get_my_free_data_page(Event &event)
{
	uint dlpn = event.get_logical_address();
	MPage current = trans_map[dlpn];
	long prev_ppn = current.ppn;
	uint block_idx = currentDataPage / BLOCK_SIZE;
	uint block_target = get_similar_data_block(dlpn);
	if(block_target == -1) {
		print_ftl_statistics();
	}
	printf("block target: %d\n", block_target);
	printf("currentDataPage: %d -> ", currentDataPage);
	currentDataPage = block_target * BLOCK_SIZE + AMT_block[block_target].pageCount;
	AMT_block[block_target].pageCount++;
	printf("%d\n", currentDataPage);
	return currentDataPage;
}

void FtlImpl_My1::AMT_table_update(uint lpn, double start_time)
{
	if (AMT_table[lpn].count) {
		AMT_table[lpn].timeTaken = (start_time - AMT_table[lpn].firstTime) / AMT_table[lpn].count;
	}
	else {
		AMT_table[lpn].firstTime = start_time;
	}
	AMT_table[lpn].count++;
	printf("AMT_table[lpn].timeTaken: %lf\n", AMT_table[lpn].timeTaken);
}

void FtlImpl_My1::AMT_block_update(uint lpn, long prev_ppn, long cur_ppn)
{

	// printf("%f\n", start_time);
	// before update PAGE AMT table, we have to modify the BLOCK AMT table
	uint pbi = prev_ppn / BLOCK_SIZE; // prev block idx
	if (AMT_table[lpn].count > 2) { // time taken 값이 존재하고, AMT_block 값에 관여되어 있다. 없애줘야 함.
		// printf("AMT_block[pbi].timeTaken: %lf\n", AMT_block[pbi].timeTaken);
		// printf("AMT_block[pbi].pageCount: %d\n", AMT_block[pbi].pageCount);
		// printf("AMT_table[lpn].timeTaken: %lf\n", AMT_table[lpn].timeTaken);
		if(AMT_block[pbi].pageCount == 1)
			AMT_block[pbi].timeTaken = 0;
		else
			AMT_block[pbi].timeTaken = (AMT_block[pbi].timeTaken * AMT_block[pbi].validCount - AMT_table[lpn].timeTaken) / (AMT_block[pbi].validCount - 1);
		// printf("AMT_block[pbi].timeTaken -> %lf\n", AMT_block[pbi].timeTaken);
	}
	if (AMT_table[lpn].count > 1) AMT_block[pbi].validCount--;

	uint cbi = cur_ppn / BLOCK_SIZE; // current block idx
	if (AMT_table[lpn].count > 1) {
		// printf("AMT_block[cbi].timeTaken: %lf\n", AMT_block[cbi].timeTaken);
		// printf("AMT_block[cbi].pageCount: %d\n", AMT_block[cbi].pageCount);
		// printf("AMT_table[lpn].timeTaken: %lf\n", AMT_table[lpn].timeTaken);
		AMT_block[cbi].timeTaken = (AMT_block[cbi].timeTaken * AMT_block[cbi].validCount + AMT_table[lpn].timeTaken) / (AMT_block[cbi].validCount + 1);
		// printf("AMT_block[cbi].timeTaken -> %lf\n", AMT_block[cbi].timeTaken);
		if(AMT_block[cbi].timeTaken < 0) AMT_block[cbi].timeTaken = 0;
	}
	AMT_block[cbi].validCount++;
}

enum status FtlImpl_My1::write(Event &event)
{
	uint dlpn = event.get_logical_address();

	// 1. time flow
	if (event.get_start_time() != prev_start_time) {
		double time_gap = event.get_start_time() - prev_start_time;
		// time flow subtraction
		for(uint i = 0; i < NUMBER_OF_ADDRESSABLE_BLOCKS; i++) {			
			if(AMT_block[i].timeTaken < time_gap) AMT_block[i].timeTaken = 0;
			else AMT_block[i].timeTaken -= time_gap;
		}
	}
	printf("time:%lf / dlpn: %d (count: %d)\n", event.get_start_time(), dlpn, AMT_table[dlpn].count);
	resolve_mapping(event, true);


	// 2. AMT_table update
	AMT_table_update(dlpn, event.get_start_time());
	
	// 3. get similar block
	// Important order. As get_free_data_page might change current.
	long free_page = get_my_free_data_page(event);
	MPage current = trans_map[dlpn];
	long prev_ppn = current.ppn;
	Address a = Address(current.ppn, PAGE);
	if (current.ppn != -1)
		event.set_replace_address(a);

	update_translation_map(current, free_page);
	trans_map.replace(trans_map.begin()+dlpn, current);

	Address b = Address(free_page, PAGE);
	event.set_address(b);

	controller.stats.numFTLWrite++;

	// 4. AMT_block update
	AMT_block_update(dlpn, prev_ppn, current.ppn);
	AMT_table[dlpn].blockidx = current.ppn / BLOCK_SIZE;
	
	 for(uint i = 0; i < NUMBER_OF_ADDRESSABLE_BLOCKS; i++) {
	 	printf("%d %lf / page: %d / valid: %d\n", i, AMT_block[i].timeTaken, AMT_block[i].pageCount, AMT_block[i].validCount);
	 }
	prev_start_time = event.get_start_time();
	return controller.issue(event);
}

enum status FtlImpl_My1::trim(Event &event)
{
	printf("trim start - ");
	uint dlpn = event.get_logical_address();

	event.set_address(Address(0, PAGE));

	MPage current = trans_map[dlpn];

	if (current.ppn != -1)
	{
		Address address = Address(current.ppn, PAGE);
		Block *block = controller.get_block_pointer(address);
		block->invalidate_page(address.page);

		evict_specific_page_from_cache(event, dlpn);

		update_translation_map(current, -1);

		trans_map.replace(trans_map.begin()+dlpn, current);
	}

	controller.stats.numFTLTrim++;
	printf("end\n");
	return controller.issue(event);
}

void FtlImpl_My1::cleanup_block(Event &event, Block *block)
{
	std::map<long, long> invalidated_translation;
	/*
	* 1. Copy only valid pages in the victim block to the current data block
	* 2. Invalidate old pages
	* 3. mark their corresponding translation pages for update
	*/
	for (uint i=0;i<BLOCK_SIZE;i++)
	{
		assert(block->get_state(i) != EMPTY);
		// When valid, two events are create, one for read and one for write. They are chained and the controller are
		// called to execute them. The execution time is then added to the real event.
		if (block->get_state(i) == VALID)
		{
			// Set up events.
			Event readEvent = Event(READ, event.get_logical_address(), 1, event.get_start_time());
			readEvent.set_address(Address(block->get_physical_address()+i, PAGE));

			// Execute read event
			if (controller.issue(readEvent) == FAILURE)
				printf("Data block copy failed.");

			// Get new address to write to and invalidate previous
			Event writeEvent = Event(WRITE, event.get_logical_address(), 1, event.get_start_time()+readEvent.get_time_taken());
			Address dataBlockAddress = Address(get_free_data_page(event, false), PAGE);

			writeEvent.set_address(dataBlockAddress);

			writeEvent.set_replace_address(Address(block->get_physical_address()+i, PAGE));

			// Setup the write event to read from the right place.
			writeEvent.set_payload((char*)page_data + (block->get_physical_address()+i) * PAGE_SIZE);

			if (controller.issue(writeEvent) == FAILURE)
				printf("Data block copy failed.");

			event.incr_time_taken(writeEvent.get_time_taken() + readEvent.get_time_taken());

			// Update GTD
			long dataPpn = dataBlockAddress.get_linear_address();

			// vpn -> Old ppn to new ppn
			//printf("%li Moving %li to %li\n", reverse_trans_map[block->get_physical_address()+i], block->get_physical_address()+i, dataPpn);
			invalidated_translation[reverse_trans_map[block->get_physical_address()+i]] = dataPpn;

			// Statistics
			controller.stats.numFTLRead++;
			controller.stats.numFTLWrite++;
			controller.stats.numWLRead++;
			controller.stats.numWLWrite++;
			controller.stats.numMemoryRead++; // Block->get_state(i) == VALID
			controller.stats.numMemoryWrite =+ 3; // GTD Update (2) + translation invalidate (1)
		}
	}

	/*
	* Perform batch update on the marked translation pages
	* 1. Update GDT and CMT if necessary.
	* 2. Simulate translation page updates.
	*/

	std::map<long, bool> dirtied_translation_pages;

	for (std::map<long, long>::const_iterator i = invalidated_translation.begin(); i!=invalidated_translation.end(); ++i)
	{
		long real_vpn = (*i).first;
		long newppn = (*i).second;

		// Update translation map ( it also updates the CMT, as it is stored inside the GDT )
		MPage current = trans_map[real_vpn];

		update_translation_map(current, newppn);

		if (current.cached)
			current.modified_ts = event.get_start_time();
		else
		{
			current.modified_ts = event.get_start_time();
			current.create_ts = event.get_start_time();
			current.cached = true;
			cmt++;
		}

		trans_map.replace(trans_map.begin()+real_vpn, current);
	}

}

void FtlImpl_My1::print_ftl_statistics()
{
	Block_manager::instance()->print_statistics();
}