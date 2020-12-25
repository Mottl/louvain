// Copyright 2020 Dmitry A. Mottl. All rights reserved.
// Use of this source code is governed by MIT license
// that can be found in the LICENSE file.

// Louvain algorithm of non-overlapping community detection
package main

import (
	"fmt"
	"os"
	"io"
	"bufio"
	"strings"
	"strconv"
	"math"
	"time"
)

func sumOverMap(d map[int32]int32) int32 {
	var sum int32
	for _, v := range d {
		sum += v
	}
	return sum
}

// Graph implements undirected graph
type Graph struct {
	Edges []int32 // plain list of edges, even and odd elements are connected (0,1), (2,3), etc.

	NodesToClusters []int32 // node -> cluster correspondence
	ClustersToNodes [][]int32 // cluster -> list of nodes correspondence
	N int32 // number of clusters

	// used in step 1:
	Degrees []int32 // node -> degree correspondence

	// used in step 2:
	InnerWeights []int32 // inner weights (doubled sum of edges inside a cluster) of clusters
	OuterWeights []map[int32]int32 // outer weights. Index - cluster id, elements - map[neighbour_id]weight

	_neighbours  [][]int32
}

// Returns neighbour nodes for the given node
func (graph *Graph) GetNeighbours(node int32) []int32 {
	if graph._neighbours[node] != nil {
		return graph._neighbours[node]
	}

	var neighbours = make([]int32, 0, 128)
	for i, n := range graph.Edges {
		if n == node {
			if i%2 == 0 { // even
				neighbours = append(neighbours, graph.Edges[i+1]) // take the next element
			} else {
				neighbours = append(neighbours, graph.Edges[i-1]) // take the previous element
			}
		}
	}
	graph._neighbours[node] = neighbours
	return neighbours
}

// Step 1: Optimize modularity. Returns the sum of dQ of all node movements.
func (graph *Graph) step1_OptimizeModularity() float64 {
	var startTime int64 = time.Now().UnixNano()
	var sum_dQ float64
	var E = float64(len(graph.Edges)/2) // 2 nodes per edge

	var sumDensity, newSumDensity float64
	for c, nodes := range graph.ClustersToNodes {
		if nodes == nil || len(nodes) == 0 {
			continue
		}
		if len(nodes) == 1 {
			sumDensity++
		} else {
			sumDensity += float64(graph.InnerWeights[c])/float64(len(nodes) * (len(nodes)-1))
		}
	}

	for A, clusterA := range graph.NodesToClusters { // iterate over all nodes
		if A%10000 == 0 {
			c := 0
			for _, v := range graph.OuterWeights {
				if v != nil {
					c++
				}
			}
			fmt.Printf("[node %d] n=|C|=%d, sum_dQ=%.6f (elapsed time: %.3fs)\n", A, graph.N, sum_dQ, float64(time.Now().UnixNano()-startTime)/1e9)
			startTime = time.Now().UnixNano()
		}

		var max_dQ float64 = math.Inf(-1) // minus infinity
		//var max_dM, max_dR float64
		var moveTo int32 = -1

		var numEdges = make(map[int32]int32, graph.Degrees[A]) // number of edges between this node and clusters. key = cluster id, value = number of edges
		neighboursOfA := graph.GetNeighbours(int32(A))
		//var maxEdges, maxDegree, candidateCluster int32

		for _, B := range neighboursOfA {
			c := graph.NodesToClusters[B]
			if _, ok := numEdges[c]; !ok {
				numEdges[c] = 1
			} else {
				numEdges[c]++
			}
			/*
			if numEdges[c] >= maxEdges {
				if numEdges[c] == maxEdges {
					if graph.Degrees[B] > maxDegree {
						maxDegree = graph.Degrees[B]
						candidateCluster = c
					}
				} else {
					maxDegree = graph.Degrees[B]
					maxEdges = numEdges[c]
					candidateCluster = c
				}
			}*/
		}

		var sumDegrees_cA_before, sumDegrees_cA_after int32
		//sumDegrees_cA_before = graph.InnerWeights[clusterA] + sumOverMap(graph.OuterWeights[clusterA])
		for _, node := range graph.ClustersToNodes[clusterA] {
			sumDegrees_cA_before += graph.Degrees[node]
		}
		sumDegrees_cA_after = sumDegrees_cA_before - graph.Degrees[A] // A goes to cluster of B
		//sumDegrees_cA_after = sumDegrees_cA_before - sumOverMap(graph.numEdges[A]) // A goes to cluster of B

		var dMA float64 = - math.Pow(float64(sumDegrees_cA_after)/2/E, 2) + math.Pow(float64(sumDegrees_cA_before)/2/E, 2)

		//var candidates [1]int32
		//candidates[0] = candidateCluster
		for clusterB, _ := range numEdges {
		//for _, B := range neighboursOfA {
		//for _, B := range candidates {
			//clusterB := graph.NodesToClusters[B]
			if clusterA == clusterB {
				continue // skip the same cluster
			}
			/*
			if numEdges[clusterB] < numEdges[clusterA] { // skip clusters with low connections
				continue
			}*/

			// modularity changes
			var dM1 float64 = float64(numEdges[clusterB] - numEdges[clusterA]) / E

			var sumDegrees_cB_before, sumDegrees_cB_after int32
			for _, node := range graph.ClustersToNodes[clusterB] {
				sumDegrees_cB_before += graph.Degrees[node]
			}
			sumDegrees_cB_after = sumDegrees_cB_before + graph.Degrees[A] // A goes to cluster of B

			var dMB float64 = - math.Pow(float64(sumDegrees_cB_after)/2/E, 2) + math.Pow(float64(sumDegrees_cB_before)/2/E, 2)
			var dM = dM1 + dMA + dMB

			// regularization changes
			var dR, R_before, R_after float64
			var density_cA_before, density_cB_before, density_cA_after, density_cB_after float64

			// calculate density of A before
			if len(graph.ClustersToNodes[clusterA]) == 1 {
				density_cA_before = 1
			} else {
				density_cA_before = float64(graph.InnerWeights[clusterA]) / float64(len(graph.ClustersToNodes[clusterA]) * (len(graph.ClustersToNodes[clusterA]) - 1))
			}

			// calculate density of B before
			if len(graph.ClustersToNodes[clusterB]) == 1 {
				density_cB_before = 1
			} else {
				density_cB_before = float64(graph.InnerWeights[clusterB]) / float64(len(graph.ClustersToNodes[clusterB]) * (len(graph.ClustersToNodes[clusterB]) - 1))
			}

			R_before = 0.5 * sumDensity / float64(graph.N)

			// calculate density of A after
			var isNchanged bool // is the number of clusters changed during movement of A?
			if len(graph.ClustersToNodes[clusterA]) == 1 { // node goes away from cA: |c| <- |c| - 1
				density_cA_after = 0
				isNchanged = true
			} else if len(graph.ClustersToNodes[clusterA]) == 2 {
				density_cA_after = 1
			} else {
				density_cA_after = float64(graph.InnerWeights[clusterA] - 2*numEdges[clusterA]) / float64((len(graph.ClustersToNodes[clusterA])-1) * (len(graph.ClustersToNodes[clusterA]) - 2))
			}

			// calculate density of B after
			density_cB_after = float64(graph.InnerWeights[clusterB] + 2*numEdges[clusterB]) / float64((len(graph.ClustersToNodes[clusterB])+1) * len(graph.ClustersToNodes[clusterB]))

			if isNchanged {
				R_after = (sumDensity+density_cA_after-density_cA_before+density_cB_after-density_cB_before) / float64(graph.N-1) / 2
			} else {
				R_after = (sumDensity+density_cA_after-density_cA_before+density_cB_after-density_cB_before) / float64(graph.N) / 2
			}

			dR = R_after - R_before
			if isNchanged {
				dR += 1/float64(len(graph.Degrees))/2
			}

			var dQ = dM + dR
			if dQ > max_dQ {
				max_dQ = dQ
				//max_dM = dM
				//max_dR = dR
				moveTo = clusterB // move to the cluster of B
				newSumDensity = sumDensity+density_cA_after-density_cA_before+density_cB_after-density_cB_before
			}
		}
		if max_dQ > 0 { // move A node to another cluster
			graph.MoveNode(int32(A), moveTo, numEdges)
			sum_dQ += max_dQ
			sumDensity = newSumDensity
		}
	}
	return sum_dQ
}

// Step 2: Merge clusters. Returns the sum of dQ of all clusters aggregations.
func (graph *Graph) step2_MergeClusters() float64 {
	var sum_dQ float64
	var E = float64(len(graph.Edges)/2) // 2 nodes per edge

	var sumDensity, newSumDensity float64
	for c, nodes := range graph.ClustersToNodes {
		if nodes == nil || len(nodes) == 0 {
			continue
		}
		if len(nodes) == 1 {
			sumDensity++
		} else {
			sumDensity += float64(graph.InnerWeights[c])/float64(len(nodes) * (len(nodes)-1))
		}
	}

	iter := 0
	for cA, _ := range graph.OuterWeights { // loop over all clusters
		if graph.OuterWeights[cA] == nil { // empty cluster - skip
			continue
		}
		if iter%1000 == 0 {
			c := 0
			for _, v := range graph.OuterWeights {
				if v != nil {
					c++
				}
			}
			fmt.Printf("[cluster %d] n=|C|=%d, sum_dQ=%.6f\n", iter, graph.N, sum_dQ)
		}
		iter++

		var max_dQ float64 = math.Inf(-1) // minus infinity
		var moveFrom, moveTo int32 = -1, -1

		var dM, MA, MB, M_after float64 // MA, MB — modularity of A and B, M_after — modularity of the aggr. cluster

		// sum of degrees equals to inner weights + outer weights:
		sumDegreeAI := graph.InnerWeights[cA]
		for _, w := range graph.OuterWeights[cA] {
			sumDegreeAI += w
		}
		sumDegreeA := float64(sumDegreeAI) / E / 2
		EinA := graph.InnerWeights[cA] / 2
		MA = float64(EinA)/E - sumDegreeA * sumDegreeA

		var sumDegreePartial_afterI int32
		for _, node := range graph.ClustersToNodes[cA] {
			sumDegreePartial_afterI += graph.Degrees[node]
		}

		for cB, _ := range graph.OuterWeights[cA] {
			var dQ float64

			sumDegreeBI := graph.InnerWeights[cB]
			for _, w := range graph.OuterWeights[cB] {
				sumDegreeBI += w
			}
			sumDegreeB := float64(sumDegreeBI) / E / 2
			EinB := graph.InnerWeights[cB] / 2
			MB = float64(EinB)/E - sumDegreeB * sumDegreeB

			var sumDegree_afterI int32 = sumDegreePartial_afterI
			for _, node := range graph.ClustersToNodes[cB] {
				sumDegree_afterI += graph.Degrees[node]
			}
			var sumDegree_after float64 = float64(sumDegree_afterI) / E / 2
			M_after = float64((graph.InnerWeights[cA] + graph.InnerWeights[cB])/2 + graph.OuterWeights[cA][cB])/E - sumDegree_after * sumDegree_after
			dM = M_after - MA - MB

			// regularization changes
			var dR, R_before, R_after float64
			var density_cA, density_cB, density_after float64

			// calculate density of A before
			if len(graph.ClustersToNodes[cA]) == 1 {
				density_cA = 1
			} else {
				density_cA = 2 * float64(graph.InnerWeights[cA]) / float64(len(graph.ClustersToNodes[cA]) * (len(graph.ClustersToNodes[cA]) - 1))
			}

			// calculate density of B before
			if len(graph.ClustersToNodes[cB]) == 1 {
				density_cB = 1
			} else {
				density_cB = 2 * float64(graph.InnerWeights[cB]) / float64(len(graph.ClustersToNodes[cB]) * (len(graph.ClustersToNodes[cB]) - 1))
			}

			//R_before = 0.5 * ((density_cA+density_cB) / float64(graph.N))
			R_before = 0.5 * (sumDensity / float64(graph.N))

			EinAggr := (graph.InnerWeights[cA] + graph.InnerWeights[cB])/2 + graph.OuterWeights[cA][cB] // divide by two 'cause weight is 2 times the number of inner edges
			c_after := len(graph.ClustersToNodes[cA]) + len(graph.ClustersToNodes[cB])
			density_after = 2 * float64(EinAggr) / float64(c_after * (c_after - 1))

			R_after = 0.5 * (sumDensity+density_after-density_cA-density_cB) / float64(graph.N-1)
			dR = R_after - R_before + 0.5/float64(len(graph.Degrees))
			dQ = dM + dR

			if dQ > max_dQ {
				max_dQ = dQ
				if graph.InnerWeights[cA] >= graph.InnerWeights[cB] {
					moveFrom = cB // from B to A
					moveTo = int32(cA)
				} else {
					moveFrom = int32(cA) // from A to B
					moveTo = cB
				}
				newSumDensity = sumDensity+density_after-density_cA-density_cB
			}
		}

		if max_dQ > 0 {
			if graph.ClustersToNodes[moveFrom] == nil {
				panic(fmt.Sprint("graph.ClustersToNodes[moveFrom] is nil. moveFrom=%d\n", moveFrom))
			}
			graph.MergeClusters(moveFrom, moveTo)
			sumDensity = newSumDensity
			sum_dQ += max_dQ
		}
	}

	return sum_dQ
}

// Moves node to another cluster
func (graph *Graph) MoveNode(node, moveTo int32, numEdges map[int32]int32) {
	moveFrom := graph.NodesToClusters[node]
	graph.NodesToClusters[node] = moveTo

	if graph.OuterWeights[moveTo] == nil {
		fmt.Println("Moving %d to %d. OuterWeights is nil\n")
		panic("!")
	}

	// Update ClusterToNodes list:
	graph.ClustersToNodes[moveTo] = append(graph.ClustersToNodes[moveTo], node)
	for i, n := range graph.ClustersToNodes[moveFrom] {
		if n == node {
			if len(graph.ClustersToNodes[moveFrom]) == 1 {
				graph.ClustersToNodes[moveFrom] = nil // free up space
				graph.N-- // decrease the number of clusters
				graph.InnerWeights[moveFrom] = 0
				graph.OuterWeights[moveFrom] = nil
			} else {
				// remove the one element
				graph.ClustersToNodes[moveFrom] = append(graph.ClustersToNodes[moveFrom][:i], graph.ClustersToNodes[moveFrom][i+1:]...)
			}
			break
		}
	}

	// Update weights
	for c, w := range numEdges {
		if c == moveFrom {
			if graph.ClustersToNodes[moveFrom] != nil {
				graph.InnerWeights[moveFrom] -= w * 2
			}
		} else if c == moveTo {
			graph.InnerWeights[c] += w * 2

			if graph.ClustersToNodes[moveFrom] == nil {
				delete(graph.OuterWeights[c], moveFrom)
			} else {
				diff := numEdges[moveFrom] - numEdges[c]
				graph.OuterWeights[c][moveFrom] += diff
				graph.OuterWeights[moveFrom][c] += diff
				if graph.OuterWeights[c][moveFrom] == 0 {
					delete(graph.OuterWeights[c], moveFrom)
					delete(graph.OuterWeights[moveFrom], c)
				}
			}
		} else {
			if graph.ClustersToNodes[moveFrom] == nil {
				delete(graph.OuterWeights[c], moveFrom)
			} else {
				graph.OuterWeights[c][moveFrom] -= w // removes connection
				graph.OuterWeights[moveFrom][c] -= w
				if graph.OuterWeights[c][moveFrom] == 0 {
					delete(graph.OuterWeights[c], moveFrom)
					delete(graph.OuterWeights[moveFrom], c)
				}
			}
			graph.OuterWeights[c][moveTo] += w // adds connection
			graph.OuterWeights[moveTo][c] += w
		}
	}
}

// Merges the first cluster to the second cluster
func (graph *Graph) MergeClusters(moveFrom, moveTo int32) {
	// move all nodes to a new cluster:

	graph.ClustersToNodes[moveTo] = append(graph.ClustersToNodes[moveTo], graph.ClustersToNodes[moveFrom]...)
	for _, A := range graph.ClustersToNodes[moveFrom] {
		graph.NodesToClusters[A] = moveTo
	}
	graph.ClustersToNodes[moveFrom] = nil // empty cluster
	graph.N-- // decrease the number of clusters

	// merge inner weights:
	graph.InnerWeights[moveTo] = graph.InnerWeights[moveFrom] + graph.InnerWeights[moveTo] + 2*graph.OuterWeights[moveFrom][moveTo]

	// merge outer weights:
	for c, w := range graph.OuterWeights[moveFrom] {
		if c != moveTo {
			if _, ok := graph.OuterWeights[moveTo][c]; ok { // 
				graph.OuterWeights[moveTo][c] += w
				if graph.OuterWeights[c] == nil {
					fmt.Printf("Nil c=%d: w=%d, InnerWeights=%d, OuterWeights=%v\n", c, w, graph.InnerWeights[c], graph.OuterWeights[c])
				}
				graph.OuterWeights[c][moveTo] += w
			} else {
				if w != 0 { // sanity check
					graph.OuterWeights[moveTo][c] = w
					if graph.OuterWeights[c] == nil {
						fmt.Printf("Merge clusters %d -> %d. Neighbour %d has weight of %d\n", moveFrom, moveTo, c, w)
						fmt.Printf("Cluster %d: %v\n", c, graph.ClustersToNodes[c])
					}
					graph.OuterWeights[c][moveTo] = w
				}
			}
		}
		delete(graph.OuterWeights[c], moveFrom)
	}

	// zero inner and outer weight for moveFrom cluster:
	graph.InnerWeights[moveFrom] = 0
	graph.OuterWeights[moveFrom] = nil
}

// Louvain function implements Louvain algorithm of non-overlapping community detection
func (graph *Graph) Louvain() []LogRow {
	if (graph == nil) || (graph.Edges == nil) {
		panic("Graph is uninitialized. Use graph := LoadFromStdin() to load data")
	}

	graph.NodesToClusters = make([]int32, graph.N, graph.N)
	graph.ClustersToNodes = make([][]int32, graph.N, graph.N)

	for j, _ := range graph.NodesToClusters {
		graph.NodesToClusters[j] = int32(j) // put each node in its own cluster
	}

	for j, _ := range graph.ClustersToNodes {
		graph.ClustersToNodes[j] = make([]int32, 1, 1)
		graph.ClustersToNodes[j][0] = int32(j) // put each node it its own cluster
	}

	// Create initial inner and outer weights for the whole clusters
	graph.InnerWeights = make([]int32, len(graph.ClustersToNodes)) // defaults to 0
	graph.OuterWeights = make([]map[int32]int32, len(graph.ClustersToNodes))

	graph.Degrees = make([]int32, graph.N, graph.N)
	graph._neighbours = make([][]int32, len(graph.Degrees), len(graph.Degrees))
	fmt.Println("Populating neighbours")
	for i:=0; i<len(graph.Edges)/2; i++ {
		node1, node2 := graph.Edges[i*2], graph.Edges[i*2+1]
		graph.Degrees[node1]++
		graph.Degrees[node2]++
		if graph.OuterWeights[node1] == nil {
			graph.OuterWeights[node1] = make(map[int32]int32)
		}
		if graph.OuterWeights[node2] == nil {
			graph.OuterWeights[node2] = make(map[int32]int32)
		}
		graph.OuterWeights[node1][node2] = 1 // create initial weights between single-element clusters
		graph.OuterWeights[node2][node1] = 1

		if graph._neighbours[node1] == nil {
			graph._neighbours[node1] = make([]int32, 0)
		}
		if graph._neighbours[node2] == nil {
			graph._neighbours[node2] = make([]int32, 0)
		}
		graph._neighbours[node1] = append(graph._neighbours[node1], node2)
		graph._neighbours[node2] = append(graph._neighbours[node2], node1)
	}
	fmt.Println("Finished populating neighbours")

	logs := make([]LogRow, 0, 256)
	Q, M, R := graph.Q()
	logs = append(logs, LogRow{"Initial one-per-node clustering", Q})
	fmt.Printf("Initial Q=%.6f, M=%.6f, R=%.6f\n", Q, M, R)
	var i int
	for {
		fmt.Printf("Modularity optimization %d:\n", i)
		startTime := time.Now().UnixNano()
		dQ1 := graph.step1_OptimizeModularity()
		Q, M, R := graph.Q()
		logs = append(logs, LogRow{"Step 1", Q})
		fmt.Printf("Modularity optimization %d result: Q=%.6f, M=%.6f, R=%.6f, dQ=%.6f  (elapsed time: %.3fs)\n", i, Q, M, R, Q-logs[len(logs)-2].Q, float64(time.Now().UnixNano()-startTime)/1e9)

		fmt.Printf("Clusters aggregation %d:\n", i)
		startTime = time.Now().UnixNano()
		dQ2 := graph.step2_MergeClusters()
		Q, M, R = graph.Q()
		logs = append(logs, LogRow{"Step 2", Q})
		fmt.Printf("Clusters aggregation %d result: Q=%.6f, M=%.6f, R=%.6f, dQ=%.6f  (elapsed time: %.3fs)\n", i, Q, M, R, Q-logs[len(logs)-2].Q, float64(time.Now().UnixNano()-startTime)/1e9)

		if dQ1 == 0 && dQ2 == 0 {
			fmt.Printf("Breaks on iteration %d\n", i)
			break
		}
		i++
	}

	return logs
}

// Provides a sanity check (finds orphans in OuterWeights)
func (graph *Graph) SanityCheck() {
	for i, m := range graph.OuterWeights {
		if m != nil {
			for c, w := range m {
				if graph.OuterWeights[c] == nil {
					fmt.Printf("orphan in %d: %d (weight=%d)\n", i, c, w)
				}
			}
		}
	}
}

// Calculates Q as M+R. Returns Q, M and R
func (graph *Graph) Q() (float64, float64, float64) {
	var Q, M, R float64
	var sumDensity float64
	var E = float64(len(graph.Edges)/2) // 2 nodes per edge

	var sumEin int32
	var count int
	for c, nodes := range graph.ClustersToNodes {
		if nodes == nil || len(nodes) == 0 { // skip empty clusters
			continue
		}

		sumEin += graph.InnerWeights[c] / 2

		/*var degrees int32
		for _, n := range nodes {
			degrees += graph.Degrees[n]
		}

		var M_ float64 = float64(graph.InnerWeights[c])/2/E - math.Pow(float64(degrees)/2/E, 2)
		*/
		var M_ float64 = - math.Pow(
			float64(graph.InnerWeights[c] + sumOverMap(graph.OuterWeights[c]))/2/E,
			2)

		var density float64
		if len(nodes) ==1 {
			density = 1
		} else {
			density = float64(graph.InnerWeights[c]) / float64(len(nodes) * (len(nodes)-1))
		}
		sumDensity += density
		M += M_
		count++
	}
	M += float64(sumEin) / E
	R = (sumDensity/float64(graph.N) - float64(graph.N)/float64(len(graph.Degrees))) / 2
	Q = M + R

	return Q, M, R
}

// Loads data from file and returns a graph struct
func LoadFromFile(filename string) Graph {
	var dataFile *os.File
	var err error
	if dataFile, err = os.Open(filename); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(-1)
	}

	var numEdges int = 0 // number
	var a_, b_, N_ int
	scanner := bufio.NewScanner(dataFile)
	for scanner.Scan() {
		strIds := strings.Split(scanner.Text(), " ")
		if len(strIds) != 2 {
			fmt.Fprintf(os.Stderr, "Invalid format: expected 2 ids per line, got %i in line %d\n", len(strIds), numEdges+1)
			os.Exit(-1)
		}

		if a_, err = strconv.Atoi(strIds[0]); err != nil {
			fmt.Fprintf(os.Stderr, "Invalid format: expected integer got %s in line %d\n", strIds[0], numEdges+1)
			os.Exit(-1)
		}

		if b_, err = strconv.Atoi(strIds[1]); err != nil {
			fmt.Fprintf(os.Stderr, "Invalid format: expected integer got %s in line %d\n", strIds[1], numEdges+1)
			os.Exit(-1)
		}

		if a_ < 0 || b_ < 0 {
			fmt.Fprintf(os.Stderr, "Id of a node should be greater or equal zero. Got %s %s in line %d\n", strIds[0], strIds[1], numEdges+1)
			os.Exit(-1)
		}

		if a_ > N_ {
			N_ = a_
		}

		if b_ > N_ {
			N_ = b_
		}

		numEdges++
	}
	var N = int32(N_+1) // N is the number of nodes
	if err := scanner.Err(); err != nil {
		fmt.Fprintln(os.Stderr, "reading standard input:", err)
	}

	graph := Graph{}
	graph.Edges = make([]int32, numEdges*2, numEdges*2) // list of tuples (A, B)
	graph.N = N // initial number of clusters is equal to the number of nodes

	var a, b int32
	dataFile.Seek(0, io.SeekStart)
	scanner = bufio.NewScanner(dataFile)
	i := 0
	for scanner.Scan() {
		strIds := strings.Split(scanner.Text(), " ")

		a_, _ = strconv.Atoi(strIds[0])
		b_, _ = strconv.Atoi(strIds[1])
		a, b = int32(a_), int32(b_)

		// put values in the edges slices
		graph.Edges[i*2] = a
		graph.Edges[i*2+1] = b

		i++
	}
	dataFile.Close()

	return graph
}

// Saves clusters to a file
func (graph *Graph) SaveClusters(filename string) {
	outfile, err := os.Create(filename)
    if err != nil {
        panic(err)
    }
    fileWriter := bufio.NewWriter(outfile)
	var counter int
	for _, nodes := range graph.ClustersToNodes {
		if nodes != nil && len(nodes) != 0 {
			stringNodes := make([]interface{}, len(nodes), len(nodes))
			for i, v := range nodes {
				stringNodes[i] = v
			}
			fmt.Fprintln(fileWriter, stringNodes...)
			counter++
		}
	}
	fileWriter.Flush()
	outfile.Close()
	fmt.Printf("%d clusters has been written to file %s\n", counter, filename)
}

// LogRow type contains one row of a history of M, R and Q values
type LogRow struct {
	message string
	Q float64
}

// Implements Stringer interface
func (logRow *LogRow) String() string {
	//return fmt.Sprintf("%s, Q=%.3g (M=%.3g, R=%.3g)", logRow.message, logRow.Q, logRow.M, logRow.R)
	return fmt.Sprintf("%s, Q=%.6g", logRow.message, logRow.Q)
}

func main() {
	if len(os.Args) != 2 {
		fmt.Println("Usage: louvain <input.graph> <output.communities>")
		fmt.Println()
		os.Exit(-1)
	}

	inputFilename := os.Args[1]
	partials := strings.Split(inputFilename, ".")
	if len(partials) > 1 {
		partials = partials[:len(partials)-1] // remove extenstion
	}
	partials = append(partials, "clusters") // add extenstion
	resultFilename := strings.Join(partials, ".")
	if _, err := os.Stat(resultFilename); err == nil {
		fmt.Printf("Output file %s already exists!\n", resultFilename)
		fmt.Println()
		os.Exit(-1)
	}

	// load graph from file:
	graph := LoadFromFile(os.Args[1])
	fmt.Println("Number of nodes:", graph.N)
	fmt.Println("Number of edges:", len(graph.Edges)/2)

	log := graph.Louvain()
	for _, logRow := range log {
		fmt.Println(logRow)
	}

	graph.SaveClusters(resultFilename)
}
