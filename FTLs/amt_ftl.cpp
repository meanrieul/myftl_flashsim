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

FtlImpl_AMT::FtlImpl_AMT(Controller &controller):
FtlImpl_DftlParent(controller)
{
	uint ssdSize = NUMBER_OF_ADDRESSABLE_BLOCKS * BLOCK_SIZE;
	copycnt = 0;
	AMT_table = new AvgModifiedTime[ssdSize];
	EMT_table = new BPage[NUMBER_OF_ADDRESSABLE_BLOCKS];
	pbn_to_lbn = new int[NUMBER_OF_ADDRESSABLE_BLOCKS];
	for(uint i = 0; i < NUMBER_OF_ADDRESSABLE_BLOCKS; i++) {
		pbn_to_lbn[i] = -1;
	}
	trim_map = new bool[ssdSize];
	freePage = ssdSize;
	prev_start_time = 0;
	printf("Total size to map: %uKB\n", ssdSize * PAGE_SIZE / 1024);
	printf("Using AMT-FTL.\n");
	return;
}

FtlImpl_AMT::~FtlImpl_AMT(void)
{
	delete[] AMT_table;
	delete[] EMT_table;
	return;
}

FtlImpl_AMT::BPage::BPage()
{
	this->pbn = -1;
	nextPage = 0;
	allocating = false;
	emt = 0;
	pageCount = 0;
	validCount = 0;
}
enum status FtlImpl_AMT::read(Event &event)
{
	uint dlpn = event.get_logical_address();
	resolve_mapping(event, false);

	MPage current = trans_map[dlpn];

	if (current.ppn != -1)
		event.set_address(Address(current.ppn, PAGE));
	else
	{
		event.set_address(Address(0, PAGE));
		event.set_noop(true);
	}
	

	event.incr_time_taken(RAM_READ_DELAY*2);
	controller.stats.numMemoryRead += 2; // Block-level lookup + range check
	controller.stats.numFTLRead++; // Page read

	return controller.issue(event);
}

uint FtlImpl_AMT::get_similar_data_block(uint lpn, double timeGap, Event &event) // block들 중 지금 page가 들어가기 가장 적절한 곳을 고르는 함수
{	// page의 AMT와 가장 비슷한 평균 AMT 값을 가진 block을 고르자.
	double min = 99999999999;
	int min_idx = -1;
	double dist = 0;
	double emt = AMT_table[lpn].amt - timeGap;
	for(uint i = 0; i < NUMBER_OF_ADDRESSABLE_BLOCKS; i++) {
		if(EMT_table[i].pageCount >= BLOCK_SIZE) continue;
		event.incr_time_taken(RAM_READ_DELAY);
		controller.stats.numMemoryRead += 1;
		dist = fabs(emt - EMT_table[i].emt);
		if(dist < min) {
			min = dist;
			min_idx = i;
		}
	}
	return min_idx;
}

void FtlImpl_AMT::AMT_table_update(uint lpn, double start_time, Event &event) // page 개개인에 대한 AMT 정보 업데이트
{
	event.incr_time_taken(RAM_READ_DELAY);
	controller.stats.numMemoryRead += 1;
	event.incr_time_taken(RAM_WRITE_DELAY);
	controller.stats.numMemoryWrite += 1;
	
	if (AMT_table[lpn].count) {
		AMT_table[lpn].amt = (start_time - AMT_table[lpn].firstTime) / AMT_table[lpn].count;
	}
	else {
		AMT_table[lpn].firstTime = start_time;
	}
	AMT_table[lpn].count++;
	AMT_table[lpn].lastTime = start_time;
}

void FtlImpl_AMT::EMT_table_delete(uint pbn, Event &event)
{
	event.incr_time_taken(RAM_WRITE_DELAY);
	controller.stats.numMemoryWrite += 1;
	int dlbn = pbn_to_lbn[pbn / BLOCK_SIZE];
	// printf("EMT_table_delete(dlbn): %d\n", dlbn);
	EMT_table[dlbn].pbn = -1;
	EMT_table[dlbn].nextPage = 0;
	EMT_table[dlbn].emt = 0;
	EMT_table[dlbn].pageCount = 0;
	EMT_table[dlbn].validCount = 0;
	freePage += BLOCK_SIZE;
}

void FtlImpl_AMT::EMT_table_update(uint lpn, uint pdlbn, uint dlbn, Event &event) // block 내 page들에 대하여 EMT 계산해서 업데이트
{
	event.incr_time_taken(RAM_READ_DELAY*2);
	controller.stats.numMemoryRead += 2;
	event.incr_time_taken(RAM_WRITE_DELAY*2);
	controller.stats.numMemoryWrite += 2;
	if (AMT_table[lpn].count > 2) { // time taken 값이 존재하고, EMT_table 값에 관여되어 있다. 없애줘야 함.
		if(EMT_table[pdlbn].validCount == 1)
			EMT_table[pdlbn].emt = 0;
		else {
			EMT_table[pdlbn].emt = (EMT_table[pdlbn].emt * EMT_table[pdlbn].validCount - AMT_table[lpn].amt) / (EMT_table[pdlbn].validCount - 1);
			if (EMT_table[pdlbn].emt < 0) EMT_table[pdlbn].emt = 0;

		}
	}
	if (AMT_table[lpn].count > 1) {
		if(EMT_table[pdlbn].validCount) 
		{
			EMT_table[pdlbn].validCount--;
		}
		// printf("%f, %d, %f\n", EMT_table[dlbn].emt, EMT_table[dlbn].validCount, AMT_table[lpn].amt);
		EMT_table[dlbn].emt = (EMT_table[dlbn].emt * EMT_table[dlbn].validCount + AMT_table[lpn].amt) / (EMT_table[dlbn].validCount + 1);
	}
	EMT_table[dlbn].validCount++;
}

enum status FtlImpl_AMT::write(Event &event)
{
	uint dlpn = event.get_logical_address();
	MPage current = trans_map[dlpn];
	// 1. time flow. AMT_block에는 block 내의 page들의 평균 '수정까지 남은 시간'이 들어 있다.
	// 시간의 흐른 만큼 이 값들을 깎아줘야 새로운 page가 들어가기 적절한 위치를 찾을 수 있다.
	if (event.get_start_time() != prev_start_time) {
		double time_gap = event.get_start_time() - prev_start_time;
		for(uint i = 0; i < NUMBER_OF_ADDRESSABLE_BLOCKS; i++) {			
			if(EMT_table[i].emt < time_gap) EMT_table[i].emt = 0;
			else EMT_table[i].emt -= time_gap;
		}
	}

	// 2. AMT_table update
	uint prev_blockidx = AMT_table[dlpn].blockidx;
	uint prev_pageidx = AMT_table[dlpn].pageidx;
	AMT_table_update(dlpn, event.get_start_time(), event);

	// 3. AMT값과 가장 비슷한 EMT를 가진 블록 찾기
	uint dlbn = get_similar_data_block(dlpn, 0, event);
	// Update trim map
	trim_map[dlpn] = false;

	if(AMT_table[dlpn].count > 1) 
	{
		//printf("delete block page: %d %d -> ppn: %d\n", prev_blockidx, prev_pageidx, EMT_table[prev_blockidx].pbn + prev_pageidx);
		Address add_del = Address(EMT_table[prev_blockidx].pbn + prev_pageidx, PAGE);
		if(controller.get_state(add_del) == VALID) {
			Block *block_del = controller.get_block_pointer(add_del);
			block_del->invalidate_page(add_del.page);

		}
	}
	//printf("dlbn: %d\n", dlbn);
	// Get new block if necessary
	if (EMT_table[dlbn].pbn == -1u)
	{
		Block_manager::instance()->insert_events_AMT(event, freePage);
		// Block_manager::instance()->insert_events(event);
		EMT_table[dlbn].allocating = true;
		EMT_table[dlbn].pbn = Block_manager::instance()->get_free_block(DATA, event).get_linear_address();
		EMT_table[dlbn].allocating = false;
		pbn_to_lbn[EMT_table[dlbn].pbn / BLOCK_SIZE] = dlbn;
		// printf("new block: %d, pbn: %d\n", dlbn, EMT_table[dlbn].pbn);
	}
	// for (int i = 0; i<NUMBER_OF_ADDRESSABLE_BLOCKS; i++) {
	// 	printf("%d: %d ||", i, EMT_table[i].pbn);
	// }
	// printf("\n");

	if (EMT_table[dlbn].pbn != -1u)
	{
		controller.stats.numMemoryWrite++; // Update next page
		//printf("EMT_table[dlbn].pbn: %d\n",EMT_table[dlbn].pbn);
		//printf("EMT_table[dlbn].nextPage: %d\n",EMT_table[dlbn].nextPage);
		event.incr_time_taken(RAM_WRITE_DELAY);
		event.set_address(Address(EMT_table[dlbn].pbn + EMT_table[dlbn].nextPage, PAGE));

		AMT_table[dlpn].blockidx = dlbn;
		AMT_table[dlpn].pageidx = EMT_table[dlbn].nextPage++;
	} 

	controller.stats.numMemoryRead += 3; // Block-level lookup + range check + optimal check
	event.incr_time_taken(RAM_READ_DELAY*3);
	controller.stats.numFTLWrite++; // Page writes
	// 4. EMT_table update
	current = trans_map[dlpn];

	EMT_table_update(dlpn, prev_blockidx, dlbn, event);
	EMT_table[dlbn].pageCount++;
	freePage--;
	prev_start_time = event.get_start_time();
	// print_block_status();

	return controller.issue(event);
}

enum status FtlImpl_AMT::trim(Event &event)
{
	uint dlpn = event.get_logical_address();
	uint dlbn = dlpn / BLOCK_SIZE;

	// Update trim map
	trim_map[dlpn] = true;

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
		EMT_table[dlbn].pbn = -1;
		EMT_table[dlbn].nextPage = 0;
		controller.stats.numMemoryWrite++; // Update block_map.
	}
	

	event.set_address(Address(0, PAGE));
	event.set_noop(true);

	event.incr_time_taken(RAM_READ_DELAY*2);
	controller.stats.numMemoryRead += 2; // Block-level lookup + range check
	controller.stats.numFTLTrim++; // Page trim

	return controller.issue(event);
}

void FtlImpl_AMT::cleanup_block(Event &event, Block *block)
{
	std::map<long, long> invalidated_translation;
	/*
	 * 1. Copy only valid pages in the victim block to the current data block
	 * 2. Invalidate old pages
	 * 3. mark their corresponding translation pages for update
	 */
	// printf("%dth block\n", pbn_to_lbn[block->get_physical_address()/BLOCK_SIZE]);
	for (uint i = 0; i < BLOCK_SIZE; i++)
	{
		assert(block->get_state(i) != EMPTY);
		// When valid, two events are create, one for read and one for write. They are chained and the controller are
		// called to execute them. The execution time is then added to the real event.
		if (block->get_state(i) == VALID)
		{
			int dlpn = event.get_logical_address();
			// Set up events.
			Event readEvent = Event(READ, dlpn, 1, event.get_start_time());
			readEvent.set_address(Address(block->get_physical_address()+i, PAGE));

			// Execute read event
			if (controller.issue(readEvent) == FAILURE)
				printf("Data block copy failed.");

			// Get new address to write to and invalidate previous
			Event writeEvent = Event(WRITE, dlpn, 1, event.get_start_time()+readEvent.get_time_taken());
			// 빈 공간 찾아서 저장하기, 없다면 할당하기
			int found = 0;
			for(uint i = 0; i < NUMBER_OF_ADDRESSABLE_BLOCKS; i++) {
				if(EMT_table[i].pbn != -1u && EMT_table[i].pageCount < BLOCK_SIZE) {
					currentDataPage = EMT_table[i].pbn + EMT_table[i].nextPage;
					found = 1;
					break;
				}
			}
			if(found == 0) {
				for(uint i = 0; i < NUMBER_OF_ADDRESSABLE_BLOCKS; i++)
				{
					if(EMT_table[i].pbn == -1u && EMT_table[i].allocating == false) {
						// printf("-----new block allocating: %d\n", i);
						EMT_table[i].allocating = true;
						EMT_table[i].pbn = Block_manager::instance()->get_free_block(DATA, event).get_linear_address();
						EMT_table[i].allocating = false;
						// printf("-----allocated: %d\n", EMT_table[i].pbn);
						pbn_to_lbn[EMT_table[i].pbn / BLOCK_SIZE] = i;
						freePage--;
						currentDataPage = EMT_table[i].pbn + EMT_table[i].nextPage;
						found = 1;
						break;
					}
				}
			}
			// printf("currentDataPage: %d\n", currentDataPage);
			Address dataBlockAddress = Address(currentDataPage, PAGE);
			
			
			// printf("dataBlockAddress: %d\n", dataBlockAddress.get_linear_address());
			writeEvent.set_address(dataBlockAddress);
			writeEvent.set_replace_address(Address(block->get_physical_address()+i, PAGE));
			// Setup the write event to read from the right place.
			writeEvent.set_payload((char*)page_data + (block->get_physical_address()+i) * PAGE_SIZE);

			if (controller.issue(writeEvent) == FAILURE)
				printf("Data block copy failed.");

			event.incr_time_taken(writeEvent.get_time_taken() + readEvent.get_time_taken());

			// Update GTD
			long dataPpn = dataBlockAddress.get_linear_address();
			// printf("dataPpn: %d\n", dataPpn);
			// printf("lbn: %d\n",pbn_to_lbn[dataPpn / BLOCK_SIZE]);
			AMT_table[dlpn].blockidx = pbn_to_lbn[dataPpn / BLOCK_SIZE];
			AMT_table[dlpn].pageidx = dataPpn % BLOCK_SIZE;
			EMT_table[AMT_table[dlpn].blockidx].nextPage++;
			EMT_table[AMT_table[dlpn].blockidx].pageCount++;
			EMT_table[AMT_table[dlpn].blockidx].validCount++;

			// printf("copy to %d %d\n", AMT_table[dlpn].blockidx, AMT_table[dlpn].pageidx);
			// vpn -> Old ppn to new ppn
			//printf("%li Moving %li to %li\n", reverse_trans_map[block->get_physical_address()+i], block->get_physical_address()+i, dataPpn);
			invalidated_translation[reverse_trans_map[block->get_physical_address()+i]] = dataPpn;
			copycnt++;
			printf("copycnt: %d\n", copycnt);
			// Statistics
			controller.stats.numFTLRead++;
			controller.stats.numFTLWrite++;
			controller.stats.numWLRead++;
			controller.stats.numWLWrite++;
			controller.stats.numMemoryRead++; // Block->get_state(i) == VALID
			controller.stats.numMemoryWrite =+ 3; // GTD Update (2) + translation invalidate (1)
		}
	}

	EMT_table_delete(block->physical_address, event);
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
bool FtlImpl_AMT::block_next_new()
{
	return (currentDataPage == -1 || currentDataPage % BLOCK_SIZE == BLOCK_SIZE -1);
}

void FtlImpl_AMT::print_block_status()
{
	 for(uint i = 0; i < NUMBER_OF_ADDRESSABLE_BLOCKS; i++) {
	 	printf("%d %lf / page: %d / valid: %d ||\t", i, EMT_table[i].emt, EMT_table[i].pageCount, EMT_table[i].validCount);
		if(i%4==3)printf("\n");
	}
}

void FtlImpl_AMT::print_ftl_statistics()
{
	printf("FTL Stats:\n");
	printf(" Blocks total: %i\n", NUMBER_OF_ADDRESSABLE_BLOCKS);

	Block_manager::instance()->print_statistics();}