/*
 * Copyright (c) 2010, Swedish Institute of Computer Science.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the Institute nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE INSTITUTE AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE INSTITUTE OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * This file is part of the Contiki operating system.
 *
 */

/**
 * \file
 *         The Minimum Rank with Hysteresis Objective Function (MRHOF)
 *
 *         This implementation uses the estimated number of
 *         transmissions (ETX) as the additive routing metric,
 *         and also provides stubs for the energy metric.
 *
 * \author Joakim Eriksson <joakime@sics.se>, Nicolas Tsiftes <nvt@sics.se>
 */

/**
 * \addtogroup uip6
 * @{
 */
 
/**
	Learning-Automata Objective Function (LAOF), extended from MRHOF
**/
#include "net/rpl/rpl-private.h"
#include "net/nbr-table.h"
#include "node-id.h"
#include <stdio.h>
#include <stdlib.h>
#include "cfs/cfs.h"
#include "contiki.h"
#include "../apps/powertrace/powertrace.h"

#define DEBUG DEBUG_FULL
#include "net/ip/uip-debug.h"

static void reset(rpl_dag_t *);
static void neighbor_link_callback(rpl_parent_t *, int, int);
static rpl_parent_t *best_parent(rpl_parent_t *, rpl_parent_t *);
static rpl_dag_t *best_dag(rpl_dag_t *, rpl_dag_t *);
static rpl_rank_t calculate_rank(rpl_parent_t *, rpl_rank_t);
static void update_metric_container(rpl_instance_t *);
// halikhani
//static void reset_etx_prob();
//static void learning_penalty(int packet_etx);
//static void learning_reward(int packet_etx);
//static int highest_etx();

rpl_of_t rpl_laof = {
  reset,
  neighbor_link_callback,
  best_parent,
  best_dag,
  calculate_rank,
  update_metric_container,
  1
};

/* Constants for the ETX moving average */
#define ETX_SCALE   100
#define ETX_ALPHA   90

/* Reject parents that have a higher link metric than the following. */
#define MAX_LINK_METRIC			10

/* Reject parents that have a higher path cost than the following. */
#define MAX_PATH_COST			100

/*
 * The rank must differ more than 1/PARENT_SWITCH_THRESHOLD_DIV in order
 * to switch preferred parent.
 */
#define PARENT_SWITCH_THRESHOLD_DIV	2

//(halikhani) Thresholds for LA-OF
#define LA_Threshold	25
#define LA_Negative_Threshold	4
#define ETX_COUNT	9
short int iterations = 0;
short int n_iterations = 0;
short int flag = 0;
short int flag2 = 0;
int ETX_values[9];
float probVector[9];



typedef uint16_t rpl_path_metric_t;


static rpl_path_metric_t
calculate_path_metric(rpl_parent_t *p)
{
  uip_ds6_nbr_t *nbr;
  if(p == NULL) {
    return MAX_PATH_COST * RPL_DAG_MC_ETX_DIVISOR;
  }
  nbr = rpl_get_nbr(p);
  if(nbr == NULL) {
    return MAX_PATH_COST * RPL_DAG_MC_ETX_DIVISOR;
  }
#if RPL_DAG_MC == RPL_DAG_MC_NONE
  {
    return p->rank + (uint16_t)nbr->link_metric;
  }
#elif RPL_DAG_MC == RPL_DAG_MC_ETX
  return p->mc.obj.etx + (uint16_t)nbr->link_metric;
#elif RPL_DAG_MC == RPL_DAG_MC_ENERGY
  return p->mc.obj.energy.energy_est + (uint16_t)nbr->link_metric;
//#elif RPL_DAG_MC != RPL_DAG_MC_ERAOF
//#error "Unsupported RPL_DAG_MC configured. See rpl.h."
#endif /* RPL_DAG_MC */
}

static void
reset(rpl_dag_t *dag)
{
  PRINTF("RPL: Reset LAOF\n");
}

static void
neighbor_link_callback(rpl_parent_t *p, int status, int numtx)
{

  if(iterations == 0){
	  //reset etx probabilities
	  int i;
	  for(i=0; i<ETX_COUNT; i++){
		  probVector[i] = 1/ETX_COUNT;
		  ETX_values[i] = i+1;
		  
	  }

  }
  uint16_t recorded_etx = 0;
  uint16_t packet_etx = numtx * RPL_DAG_MC_ETX_DIVISOR;
  uint16_t new_etx = 3*RPL_DAG_MC_ETX_DIVISOR;
  uip_ds6_nbr_t *nbr = NULL;

  nbr = rpl_get_nbr(p);
  if(nbr == NULL) {
    /* No neighbor for this parent - something bad has occurred */
    return;
  }
  iterations ++;
  recorded_etx = nbr->link_metric;

  //(halikhani)
  if(status == MAC_TX_NOACK){

	n_iterations ++;
  	packet_etx = MAX_LINK_METRIC * RPL_DAG_MC_ETX_DIVISOR;
	if(iterations > LA_Threshold && n_iterations == LA_Negative_Threshold){
	  //reset etx probabilities
      int i;
      for(i=0; i<ETX_COUNT; i++){
    	  probVector[i] = 1/ETX_COUNT;
    	  ETX_values[i] = i+1;
      }

	  iterations = 0;
	  n_iterations = 0;
	}
  }

  if(iterations <= LA_Threshold){
  	if(packet_etx == MAX_LINK_METRIC * RPL_DAG_MC_ETX_DIVISOR){
	    // learning penalty
  		float b = 0.1;
  		int i;
  		for(i = 0; i<ETX_COUNT ; i++){
  		if(ETX_values[i] == recorded_etx*RPL_DAG_MC_ETX_DIVISOR)
  			probVector[i] = (1 - b)*probVector[i];
  		else
  			probVector[i] = b/(ETX_COUNT - 1) + (1 - b)*probVector[i];

  		  }
	  }
	  else{
	    //learning reward
		 float a = 0.1;
		 int i;
		 for(i = 0; i<ETX_COUNT ; i++){
			 if(ETX_values[i] == numtx){
				 probVector[i] = probVector[i] + a*(1 - probVector[i]);
			 } 
		     else{
		    	 probVector[i] = (1 - a)*probVector[i]; 
		     }       
		 }
	  }
  }
  int max_idx = 88;
  if(iterations >= LA_Threshold){
	// assign highest probability
	  float max_prob_val = 0;
	  int max_prob_idx = 0;
	  int i;
	  for(i=0; i<ETX_COUNT; i++){
	      if(probVector[i] > max_prob_val){
	        max_prob_val = probVector[i];
	        max_prob_idx = i;
	        max_idx = i;
	      }
	    }
	    new_etx =  ETX_values[max_prob_idx]*RPL_DAG_MC_ETX_DIVISOR;
  }
  char show_float[20];
  ftoa(probVector[0], show_float, 4);

 
    PRINTF("RPL: ETX changed from %u to %u (packet ETX = %u), iteration no. %d,n_iteration no. %d,probVector[0] = %s",
        (unsigned)(recorded_etx / RPL_DAG_MC_ETX_DIVISOR),
        (unsigned)(new_etx / RPL_DAG_MC_ETX_DIVISOR),
        (unsigned)(packet_etx / RPL_DAG_MC_ETX_DIVISOR), iterations,n_iterations, show_float);
    /* update the link metric for this nbr */
    nbr->link_metric = new_etx;

}

static rpl_rank_t
calculate_rank(rpl_parent_t *p, rpl_rank_t base_rank)
{
  rpl_rank_t new_rank;
  rpl_rank_t rank_increase;
  uip_ds6_nbr_t *nbr;

  if(p == NULL || (nbr = rpl_get_nbr(p)) == NULL) {
    if(base_rank == 0) {
      return INFINITE_RANK;
    }
    rank_increase = RPL_INIT_LINK_METRIC * RPL_DAG_MC_ETX_DIVISOR;
  } else {
    rank_increase = nbr->link_metric;
    if(base_rank == 0) {
      base_rank = p->rank;
    }
  }

  if(INFINITE_RANK - base_rank < rank_increase) {
    /* Reached the maximum rank. */
    new_rank = INFINITE_RANK;
  } else {
   /* Calculate the rank based on the new rank information from DIO or
      stored otherwise. */
    new_rank = base_rank + rank_increase;
  }

  return new_rank;
}

static rpl_dag_t *
best_dag(rpl_dag_t *d1, rpl_dag_t *d2)
{
  if(d1->grounded != d2->grounded) {
    return d1->grounded ? d1 : d2;
  }

  if(d1->preference != d2->preference) {
    return d1->preference > d2->preference ? d1 : d2;
  }

  return d1->rank < d2->rank ? d1 : d2;
}

static rpl_parent_t *
best_parent(rpl_parent_t *p1, rpl_parent_t *p2)
{
  rpl_dag_t *dag;
  rpl_path_metric_t min_diff;
  rpl_path_metric_t p1_metric;
  rpl_path_metric_t p2_metric;

  dag = p1->dag; /* Both parents are in the same DAG. */

  min_diff = RPL_DAG_MC_ETX_DIVISOR /
             PARENT_SWITCH_THRESHOLD_DIV;

  p1_metric = calculate_path_metric(p1);
  p2_metric = calculate_path_metric(p2);

  /* Maintain stability of the preferred parent in case of similar ranks. */
  if(p1 == dag->preferred_parent || p2 == dag->preferred_parent) {
    if(p1_metric < p2_metric + min_diff &&
       p1_metric > p2_metric - min_diff) {
      PRINTF("RPL: LAOF hysteresis: %u <= %u <= %u\n",
             p2_metric - min_diff,
             p1_metric,
             p2_metric + min_diff);
      return dag->preferred_parent;
    }
  }

  return p1_metric < p2_metric ? p1 : p2;
}

#if RPL_DAG_MC == RPL_DAG_MC_NONE
static void
update_metric_container(rpl_instance_t *instance)
{
	/*
	  char message[32];
	  char buf[100];
	  strcpy(message,"#1.hello world.");
	  strcpy(buf,message);
	  printf("step 1: %s\n", buf );
	  char *filename = "/home/input.txt";
	  int fd_write, fd_read;
	  int n;
	  fd_write = cfs_open("/home/input.txt", CFS_WRITE);
	  if(fd_write != -1) {
	    n = cfs_write(fd_write, message, sizeof(message));
	    cfs_close(fd_write);
	    printf("step 2: successfully written to cfs. wrote %i bytes\n", n);
	  } else {
	    printf("ERROR: could not write to memory in step 2.\n");
	  }
	  strcpy(buf,"empty string");
	  fd_read = cfs_open(filename, CFS_READ);
	  if(fd_read!=-1) {
	    cfs_read(fd_read, buf, sizeof(message));
	    printf("step 3: %s\n", buf);
	    cfs_close(fd_read);
	  } else {
	    printf("ERROR: could not read from memory in step 3.\n");
	  }
	  strcpy(buf,"empty string");
	  strcpy(message,"#2.contiki is amazing!");
	  fd_write = cfs_open(filename, CFS_WRITE | CFS_APPEND);
	  if(fd_write != -1) {
	    n = cfs_write(fd_write, message, sizeof(message));
	    cfs_close(fd_write);
	    printf("step 4: successfully appended data to cfs. wrote %i bytes  \n",n);
	  } else {
	    printf("ERROR: could not write to memory in step 4.\n");
	  }
	  strcpy(buf,"empty string");
	  fd_read = cfs_open(filename, CFS_READ);
	  if(fd_read != -1) {
	    cfs_read(fd_read, buf, sizeof(message));
	    printf("step 5: #1 - %s\n", buf);
	    cfs_seek(fd_read, sizeof(message), CFS_SEEK_SET);
	    cfs_read(fd_read, buf, sizeof(message));
	    printf("step 5: #2 - %s\n", buf);
	    cfs_close(fd_read);
	  } else {
	    printf("ERROR: could not read from memory in step 5.\n");
	  }
	  cfs_remove(filename);
	  fd_read = cfs_open(filename, CFS_READ);
	  if(fd_read == -1) {
	    printf("Successfully removed file\n");
	  } else {
	    printf("ERROR: could read from memory in step 6.\n");
	  }*/
	//printf("hossss node_id : %u ",node_id);
	//printf("hossss node_loc_x : %u ",node_loc_x);
	//printf("hossss node_loc_y : %u ",node_loc_y);
	//printf("hossss node_loc_z : %u ",node_loc_z);
	//printf("hossss node_EnergyHarvested : %u ",node_EnergyHarvested);
  instance->mc.type = RPL_DAG_MC;
}
#else
static void
update_metric_container(rpl_instance_t *instance)
{
  rpl_path_metric_t path_metric;
  rpl_dag_t *dag;
#if RPL_DAG_MC == RPL_DAG_MC_ENERGY
  uint8_t type;
#endif

  instance->mc.type = RPL_DAG_MC;
  instance->mc.flags = RPL_DAG_MC_FLAG_P;
  instance->mc.aggr = RPL_DAG_MC_AGGR_ADDITIVE;
  instance->mc.prec = 0;

  dag = instance->current_dag;

  if (!dag->joined) {
    PRINTF("RPL: Cannot update the metric container when not joined\n");
    return;
  }

  if(dag->rank == ROOT_RANK(instance)) {
    path_metric = 0;
  } else {
    path_metric = calculate_path_metric(dag->preferred_parent);
  }

#if RPL_DAG_MC == RPL_DAG_MC_ETX
  instance->mc.length = sizeof(instance->mc.obj.etx);
  instance->mc.obj.etx = path_metric;
  //printf("aliiii: link metric: %u\n ",
		  instance->mc.obj.etx);

  //PRINTF("RPL: My path ETX to the root is %u.%u\n",
	instance->mc.obj.etx / RPL_DAG_MC_ETX_DIVISOR,
	(instance->mc.obj.etx % RPL_DAG_MC_ETX_DIVISOR * 100) /
	 RPL_DAG_MC_ETX_DIVISOR);
#elif RPL_DAG_MC == RPL_DAG_MC_ENERGY
  instance->mc.length = sizeof(instance->mc.obj.energy);

  if(dag->rank == ROOT_RANK(instance)) {
    type = RPL_DAG_MC_ENERGY_TYPE_MAINS;
  } else {
    type = RPL_DAG_MC_ENERGY_TYPE_BATTERY;
  }

  instance->mc.obj.energy.flags = type << RPL_DAG_MC_ENERGY_TYPE;
  instance->mc.obj.energy.energy_est = path_metric;
#endif /* RPL_DAG_MC == RPL_DAG_MC_ETX */
}
#endif /* RPL_DAG_MC == RPL_DAG_MC_NONE */

/** @}*/
