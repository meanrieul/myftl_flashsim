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
	AMT_block = new BPage[NUMBER_OF_ADDRESSABLE_BLOCKS];
	trim_map = new bool[NUMBER_OF_ADDRESSABLE_BLOCKS*BLOCK_SIZE];
	inuseBlock = NULL;
	prev_start_time = 0;
	printf("Total size to map: %uKB\n", ssdSize * PAGE_SIZE / 1024);
	printf("Using myFTL1.\n");
	return;
}

FtlImpl_My1::~FtlImpl_My1(void)
{
	delete[] AMT_table;
	delete[] AMT_block;
	return;
}

FtlImpl_My1::BPage::BPage()
{
	this->pbn = -1;
	nextPage = 0;
	optimal = true;
	state = FREE;
	timeTaken = 0;
	pageCount = 0;
	validCount = 0;
}
enum status FtlImpl_My1::read(Event &event)
{
	uint dlpn = event.get_logical_address();
	uint dlbn = dlpn / BLOCK_SIZE;

	// Block-level lookup
 	if (AMT_block[dlbn].optimal)
	{
		uint dppn = AMT_block[dlbn].pbn + (dlpn % BLOCK_SIZE);

		if (AMT_block[dlbn].pbn != (uint) -1)
			event.set_address(Address(dppn, PAGE));
		else
		{
			event.set_address(Address(0, PAGE));
			event.set_noop(true);
		}
	} else { // DFTL lookup
		resolve_mapping(event, false);

		MPage current = trans_map[dlpn];

		if (current.ppn != -1)
			event.set_address(Address(current.ppn, PAGE));
		else
		{
			event.set_address(Address(0, PAGE));
			event.set_noop(true);
		}
	}

	event.incr_time_taken(RAM_READ_DELAY*2);
	controller.stats.numMemoryRead += 2; // Block-level lookup + range check
	controller.stats.numFTLRead++; // Page read

	return controller.issue(event);
}

uint FtlImpl_My1::get_similar_data_block(uint lpn) // block들 중 지금 page가 들어가기 가장 적절한 곳을 고르는 함수
{	// page의 AMT와 가장 비슷한 평균 AMT 값을 가진 block을 고르자.
	// 이진 탐색을 쓸 수도?
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
		dist = fabs(AMT_table[lpn].timeTaken - AMT_block[i].timeTaken);
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
	// Important order. As get_free_data_page might change current.
	long free_page = -1;

	// Get next available data page
	if (inuseBlock == NULL)
	{
		// DFTL way
		free_page = get_free_data_page(event);
	} else {
		Address address;
		if (inuseBlock->get_next_page(address) == SUCCESS)
		{
			// Get page from biftl block space
			free_page = address.get_linear_address();
		}
		else if (blockQueue.size() != 0)
		{
			inuseBlock = blockQueue.front();
			blockQueue.pop();
			if (inuseBlock->get_next_page(address) == SUCCESS)
			{
				// Get page from the next block in the biftl block space
				free_page = address.get_linear_address();
			}
			else
			{
				assert(false);
			}
		} else {
			inuseBlock = NULL;
			// DFTL way
			free_page = get_free_data_page(event);
		}
	}

	assert(free_page != -1);

	return free_page;

}

void FtlImpl_My1::AMT_table_update(uint lpn, double start_time) // page 개개인에 대한 AMT 정보 업데이트
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

void FtlImpl_My1::AMT_block_update(uint lpn, uint pdlbn, uint dlbn) // block 내 page들에 대하여 평균을 다시 한 번 계산함
{

	// printf("%f\n", start_time);
	// before update PAGE AMT table, we have to modify the BLOCK AMT table
	if (AMT_table[lpn].count > 2) { // time taken 값이 존재하고, AMT_block 값에 관여되어 있다. 없애줘야 함.
		// printf("AMT_block[pbi].timeTaken: %lf\n", AMT_block[pbi].timeTaken);
		// printf("AMT_block[pbi].pageCount: %d\n", AMT_block[pbi].pageCount);
		// printf("AMT_table[lpn].timeTaken: %lf\n", AMT_table[lpn].timeTaken);
		if(AMT_block[pdlbn].pageCount == 1)
			AMT_block[pdlbn].timeTaken = 0;
		else
			AMT_block[pdlbn].timeTaken = (AMT_block[pdlbn].timeTaken * AMT_block[pdlbn].validCount - AMT_table[lpn].timeTaken) / (AMT_block[pdlbn].validCount - 1);
		// printf("AMT_block[pbi].timeTaken -> %lf\n", AMT_block[pbi].timeTaken);
	}
	if (AMT_block[pdlbn].validCount > 1) AMT_block[pdlbn].validCount--;

	if (AMT_table[lpn].count > 1) {
		// printf("AMT_block[cbi].timeTaken: %lf\n", AMT_block[cbi].timeTaken);
		// printf("AMT_block[cbi].pageCount: %d\n", AMT_block[cbi].pageCount);
		// printf("AMT_table[lpn].timeTaken: %lf\n", AMT_table[lpn].timeTaken);
		AMT_block[dlbn].timeTaken = (AMT_block[dlbn].timeTaken * AMT_block[dlbn].validCount + AMT_table[lpn].timeTaken) / (AMT_block[dlbn].validCount + 1);
		// printf("AMT_block[cbi].timeTaken -> %lf\n", AMT_block[cbi].timeTaken);
		if(AMT_block[dlbn].timeTaken < 0) AMT_block[dlbn].timeTaken = 0;
	}
	AMT_block[dlbn].validCount++;
}

enum status FtlImpl_My1::write(Event &event)
{
	uint dlpn = event.get_logical_address();
	MPage current = trans_map[dlpn];
	long prev_ppn = current.ppn;
	// 1. time flow. AMT_block에는 block 내의 page들의 평균 '수정까지 남은 시간'이 들어 있다.
	// 시간의 흐른 만큼 이 값들을 깎아줘야 새로운 page가 들어가기 적절한 위치를 찾을 수 있다.
	if (event.get_start_time() != prev_start_time) {
		double time_gap = event.get_start_time() - prev_start_time;
		// time flow subtraction
		for(uint i = 0; i < NUMBER_OF_ADDRESSABLE_BLOCKS; i++) {			
			if(AMT_block[i].timeTaken < time_gap) AMT_block[i].timeTaken = 0;
			else AMT_block[i].timeTaken -= time_gap;
		}
	}

	// 2. AMT_table update
	AMT_table_update(dlpn, event.get_start_time());

	// 3. get similar block
	uint prev_dlbn = AMT_table[dlpn].blockidx;
	uint dlbn = get_similar_data_block(dlpn);
	bool handled = false; // this write event handled?

	// Update trim map
	trim_map[dlpn] = false;
	
	// Block-level lookup
	if (AMT_block[dlbn].optimal)
	{
		// Optimised case for block level lookup

		// Get new block if necessary
		if (AMT_block[dlbn].pbn == -1u && dlpn % BLOCK_SIZE == 0)
			AMT_block[dlbn].pbn = Block_manager::instance()->get_free_block(DATA, event).get_linear_address();

		if (AMT_block[dlbn].pbn != -1u)
		{
			unsigned char dppn = dlpn % BLOCK_SIZE;

			controller.stats.numMemoryWrite++; // Update next page
			
			event.incr_time_taken(RAM_WRITE_DELAY);
			event.set_address(Address(AMT_block[dlbn].pbn + dppn, PAGE));
			AMT_block[dlbn].nextPage++;
			handled = true;

			// unsigned char dppn = dlpn % BLOCK_SIZE;
			// if (AMT_block[dlbn].nextPage == dppn)
			// {
			// 	controller.stats.numMemoryWrite++; // Update next page
			// 	event.incr_time_taken(RAM_WRITE_DELAY);
			// 	event.set_address(Address(AMT_block[dlbn].pbn + dppn, PAGE));
			// 	AMT_block[dlbn].nextPage++;
			// 	handled = true;
			// } else {
			// 	/*
			// 	 * Transfer the block to DFTL.
			// 	 * 1. Get number of pages to write
			// 	 * 2. Get start address for translation map
			// 	 * 3. Write mappings to trans_map
			// 	 * 4. Make block non-optimal
			// 	 * 5. Add the block to the block queue to be used later
			// 	 */

			// 	// 1-3
			// 	uint numPages = AMT_block[dlbn].nextPage;
			// 	long startAdr = dlbn * BLOCK_SIZE;

			// 	Block *b = controller.get_block_pointer(Address(startAdr, PAGE));

			// 	for (uint i=0;i<numPages;i++)
			// 	{
			// 		//assert(b->get_state(i) != INVALID);

			// 		if (b->get_state(i) != VALID)
			// 			continue;

			// 		MPage current = trans_map[startAdr + i];

			// 		if (current.ppn != -1)
			// 		{
			// 			update_translation_map(current, AMT_block[dlbn].pbn+i);
			// 			current.create_ts = event.get_start_time();
			// 			current.modified_ts = event.get_start_time();
			// 			current.cached = true;
			// 			trans_map.replace(trans_map.begin()+startAdr+i, current);

			// 			cmt++;

			// 			event.incr_time_taken(RAM_WRITE_DELAY);
			// 			controller.stats.numMemoryWrite++;
			// 		}

			// 	}

			// 	// 4. Set block to non optimal
			// 	event.incr_time_taken(RAM_WRITE_DELAY);
			// 	controller.stats.numMemoryWrite++;
			// 	AMT_block[dlbn].optimal = false;

			// 	// 5. Add it to the queue to be used later.
			// 	Block *block = controller.get_block_pointer(Address(AMT_block[dlbn].pbn, BLOCK));
			// 	if (block->get_pages_valid() != BLOCK_SIZE)
			// 	{
			// 		if (inuseBlock == NULL)
			// 			inuseBlock = block;
			// 		else
			// 			blockQueue.push(block);
			// 	}


			// 	controller.stats.numPageBlockToPageConversion++;
			// }
		} else {
			AMT_block[dlbn].optimal = false;
		}
	}

	if (!handled)
	{
		// Important order. As get_free_data_page might change current.
		long free_page = get_my_free_data_page(event);
		resolve_mapping(event, true);

		MPage current = trans_map[dlpn];

		Address a = Address(current.ppn, PAGE);

		if (current.ppn != -1)
			event.set_replace_address(a);


		update_translation_map(current, free_page);
		trans_map.replace(trans_map.begin()+dlpn, current);

		// Finish DFTL logic
		event.set_address(Address(current.ppn, PAGE));
	}

	controller.stats.numMemoryRead += 3; // Block-level lookup + range check + optimal check
	event.incr_time_taken(RAM_READ_DELAY*3);
	controller.stats.numFTLWrite++; // Page writes

	// 4. AMT_block update
	current = trans_map[dlpn];

	AMT_block_update(dlpn, prev_dlbn, dlpn);
	AMT_table[dlpn].blockidx = dlbn;
	AMT_block[dlbn].pageCount++;
	
	 for(uint i = 0; i < NUMBER_OF_ADDRESSABLE_BLOCKS; i++) {
	 	printf("%d %lf / page: %d / valid: %d\n", i, AMT_block[i].timeTaken, AMT_block[i].pageCount, AMT_block[i].validCount);
	 }
	prev_start_time = event.get_start_time();
	print_ftl_statistics();
	return controller.issue(event);
}

enum status FtlImpl_My1::trim(Event &event)
{
	uint dlpn = event.get_logical_address();
	uint dlbn = dlpn / BLOCK_SIZE;

	// Update trim map
	trim_map[dlpn] = true;

	// Block-level lookup
	if (AMT_block[dlbn].optimal)
	{
		Address address = Address(AMT_block[dlbn].pbn+event.get_logical_address()%BLOCK_SIZE, PAGE);
		Block *block = controller.get_block_pointer(address);
		block->invalidate_page(address.page);

		if (block->get_state() == INACTIVE) // All pages invalid, force an erase. PTRIM style.
		{
			AMT_block[dlbn].pbn = -1;
			AMT_block[dlbn].nextPage = 0;
			Block_manager::instance()->erase_and_invalidate(event, address, DATA);
		}
	} else { // DFTL lookup

		MPage current = trans_map[dlpn];
		if (current.ppn != -1)
		{
			Address address = Address(current.ppn, PAGE);
			Block *block = controller.get_block_pointer(address);
			block->invalidate_page(address.page);

			evict_specific_page_from_cache(event, dlpn);

			// Update translation map to default values.
			update_translation_map(current, -1);
			trans_map.replace(trans_map.begin()+dlpn, current);

			event.incr_time_taken(RAM_READ_DELAY);
			event.incr_time_taken(RAM_WRITE_DELAY);
			controller.stats.numMemoryRead++;
			controller.stats.numMemoryWrite++;
		}

		// Update trim map and update block map if all pages are trimmed. i.e. the state are reseted to optimal.
		long addressStart = dlpn - dlpn % BLOCK_SIZE;
		bool allTrimmed = true;
		for (uint i=addressStart;i<addressStart+BLOCK_SIZE;i++)
		{
			if (!trim_map[i])
				allTrimmed = false;
		}

		controller.stats.numMemoryRead++; // Trim map looping

		if (allTrimmed)
		{
			AMT_block[dlbn].pbn = -1;
			AMT_block[dlbn].nextPage = 0;
			AMT_block[dlbn].optimal = true;
			controller.stats.numMemoryWrite++; // Update block_map.
		}
	}

	event.set_address(Address(0, PAGE));
	event.set_noop(true);

	event.incr_time_taken(RAM_READ_DELAY*2);
	controller.stats.numMemoryRead += 2; // Block-level lookup + range check
	controller.stats.numFTLTrim++; // Page trim

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

// Returns true if the next page is in a new block
bool FtlImpl_My1::block_next_new()
{
	return (currentDataPage == -1 || currentDataPage % BLOCK_SIZE == BLOCK_SIZE -1);
}

void FtlImpl_My1::print_ftl_statistics()
{
	printf("FTL Stats:\n");
	printf(" Blocks total: %i\n", NUMBER_OF_ADDRESSABLE_BLOCKS);

	int numOptimal = 0;
	for (uint i=0;i<NUMBER_OF_ADDRESSABLE_BLOCKS;i++)
	{
		BPage bp = AMT_block[i];
		if (bp.optimal)
		{
			printf("Optimal: %i\n", i);
			numOptimal++;
		}

	}

	printf(" Blocks optimal: %i\n", numOptimal);
	Block_manager::instance()->print_statistics();}