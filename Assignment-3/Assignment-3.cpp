//===- Assignment-3.cpp -- Taint analysis ------------------//
//
//                     SVF: Static Value-Flow Analysis
//
// Copyright (C) <2013-2022>  <Yulei Sui>
//

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.

// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//
//===----------------------------------------------------------------------===//
/*
 * Graph reachability, Andersen's pointer analysis and taint analysis
 *
 * Created on: Feb 18, 2024
 */

#include "Assignment-3.h"
#include "WPA/Andersen.h"
#include <sys/stat.h>
#include <filesystem>
#include <fstream>
#include <sstream>
#include <string>

using namespace SVF;
using namespace llvm;
using namespace std;

/// TODO: Implement your code to parse the two lines to identify sources and sinks from `SrcSnk.txt` for your
/// reachability analysis The format in SrcSnk.txt is in the form of
/// line 1 for sources  "{ api1 api2 api3 }"
/// line 2 for sinks    "{ api1 api2 api3 }"
void ICFGTraversal::readSrcSnkFromFile(const string& filename) {
	std::ifstream inFile(filename);
	if(!inFile.is_open()){
		checker_source_api = {"source"};
		checker_sink_api = {"sink"};
		return;
	}

	std::string line;
	int braceLineNo = 0;
	while(std::getline(inFile, line)){
		size_t open = line.find('{');
		size_t close = line.rfind('}');
		if(open == std::string::npos || close == std::string::npos || close <= open){
		continue;
		}
	std::string label = line.substr(0, open);
	bool isSink;
	if(label.find("sink") != std::string::npos) {
		isSink = true;
	}
	else if(label.find("source") != std::string::npos){
		isSink = false;
	} else {
		isSink = (braceLineNo != 0);
	}
	
	std::istringstream iss(line.substr(open + 1, close - open -1));
	std::string api;
		while(iss >> api){
			if(isSink){
				checker_sink_api.insert(api);
			} else{
				checker_source_api.insert(api);
			}
		}
		++braceLineNo;
	}
	inFile.close();
}



/// TODO: Convert each collected ICFG path into a string and insert it into
/// `std::set<std::string> paths`. The path should use the format
/// "START->1->2->4->5->END", where each pair of adjacent node IDs is connected
/// by an ICFG edge, similar to Assignment 2.
void ICFGTraversal::collectICFGPath(std::vector<unsigned>& path) {
	
std::string pathStr = "START";
for(unsigned nodeID : path){
	pathStr += "->" + std::to_string(nodeID);

}

	pathStr += "->END";

	std::cout <<pathStr<<std::endl;
	paths.insert(pathStr);

}

/// TODO: Implement context-sensitive ICFG traversal from `src` to `snk` by
/// matching call and return edges while maintaining a `callstack`. Each path,
/// including loops and qualified by its callstack, should only be traversed
/// once using `visited`. Call `collectICFGPath` for every reachable path.
void ICFGTraversal::reachability(const ICFGNode* src, const ICFGNode* snk) {
	std::pair<const ICFGNode*, CallStack> currentState = std::make_pair(src, callstack);

    if(visited.count(currentState)){
        return;
    }
 
    visited.insert(currentState);

    path.push_back(src->getId());

    if(src == snk){
        collectICFGPath(path);

    }

    for(const ICFGEdge *edge : src->getOutEdges()){

        if(const CallCFGEdge *callEdge = SVFUtil::dyn_cast<CallCFGEdge>(edge)){
            callstack.push_back(callEdge->getSrcNode());
            reachability(edge->getDstNode(), snk);
            callstack.pop_back();
        } 
        else if(const RetCFGEdge *retEdge = SVFUtil::dyn_cast<RetCFGEdge>(edge)){
            
            if(!callstack.empty() && callstack.back() == retEdge->getCallSite()){
                const ICFGNode *top = callstack.back();
                callstack.pop_back();
                reachability(edge->getDstNode(), snk);
                callstack.push_back(top);
            }
            else if (callstack.empty()){
                reachability(edge->getDstNode(), snk);

            }
        
        }
        else if (SVFUtil::dyn_cast<IntraCFGEdge>(edge)){
            reachability(edge->getDstNode(), snk);
        }
            
        
    }
    visited.erase(currentState);
    path.pop_back();

}

// TODO: Implement your Andersen's Algorithm here
/// The solving rules are as follows:
/// p <--Addr-- o        =>  pts(p) = pts(p) ∪ {o}
/// q <--COPY-- p        =>  pts(q) = pts(q) ∪ pts(p)
/// q <--LOAD-- p        =>  for each o ∈ pts(p) : q <--COPY-- o
/// q <--STORE-- p       =>  for each o ∈ pts(q) : o <--COPY-- p
/// q <--GEP, fld-- p    =>  for each o ∈ pts(p) : pts(q) = pts(q) ∪ {o.fld}
/// pts(q) denotes the points-to set of q
void AndersenPTA::solveWorklist() {
	while(!isWorklistEmpty()){
		NodeID pId = popFromWorklist();
		ConstraintNode* p = consCG->getConstraintNode(pId);

		const PointsTo pts = getPts(pId);
	}
	
}

/// TODO: Checking aliases of the two variables at source and sink. For example:
/// src instruction:  actualRet = source();
/// snk instruction:  sink(actualParm,...);
/// return true if actualRet is aliased with any parameter at the snk node (e.g., via ander->alias(..,..))
bool ICFGTraversal::aliasCheck(const CallICFGNode* src, const CallICFGNode* snk) {
	const RetICFGNode* srcRet = src->getRetICFGNode();
	if(srcRet == nullptr){
		return false;
	}
	const SVFVar* actualRet = srcRet->getActualRet();
	if(actualRet == nullptr){
		return false;
	}
	NodeID srcID = actualRet->getId();

	for(const SVFVar* actualParm : snk->getActualParms()){
		if(actualParm == nullptr){
			continue;
		}

		if(ander->alias(srcID, actualParm->getId()) != SVF::AliasResult::NoAlias){
			return true;
		}
	}

	return false;
}

// Start taint checking.
// There is a tainted flow from p@source to q@sink
// if (1) alias(p,q)==true and (2) source reaches sink on ICFG.
void ICFGTraversal::taintChecking() {
	const fs::path& config = CUR_DIR() / "Tests/SrcSnk.txt";
	// configure sources and sinks for taint analysis
	readSrcSnkFromFile(config);

	// Set file permissions to read-only for user, group and others
	if (chmod(config.string().c_str(), S_IRUSR | S_IRGRP | S_IROTH) == -1) {
		std::cerr << "Error setting file permissions for " << config << ": " << std::strerror(errno) << std::endl;
		abort();
	}
	ander = new AndersenPTA(pag);
	ander->analyze();
	for (const CallICFGNode* src : identifySources()) {
		for (const CallICFGNode* snk : identifySinks()) {
			if (aliasCheck(src, snk))
				reachability(src, snk);
		}
	}
}

/*!
 * Andersen analysis
 */
void AndersenPTA::analyze() {
	initialize();
	initWorklist();
	do {
		reanalyze = false;
		solveWorklist();
		if (updateCallGraph(getIndirectCallsites()))
			reanalyze = true;
	} while (reanalyze);
	finalize();
}
