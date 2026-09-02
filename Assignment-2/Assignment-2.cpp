//===- SVF-Teaching Assignment 2-------------------------------------//
//
//     SVF: Static Value-Flow Analysis Framework for Source Code
//
// Copyright (C) <2013->
//

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//
//===-----------------------------------------------------------------------===//
/*
 // SVF-Teaching Assignment 2 : Source Sink ICFG DFS Traversal
 //
 // 
 */

#include <set>
#include "Assignment-2.h"
#include <iostream>
using namespace SVF;
using namespace std;

/// TODO: print each path once this method is called, and
/// add each path as a string into std::set<std::string> paths
/// Print the path in the format "START->1->2->4->5->END", where -> indicate an ICFGEdge connects two ICFGNode IDs

void ICFGTraversal::collectICFGPath(std::vector<unsigned> &path){

// prints the paths given in parameters
std::string pathStr = "START";
for (unsigned nodeID : path) {
    pathStr += "->" + std::to_string(nodeID);

}
    pathStr += "->END";

    std::cout<<pathStr<<std::endl;
    paths.insert(pathStr);

}


/// TODO: Implement your context-sensitive ICFG traversal here to traverse each program path (once for any loop) from src to dst
void ICFGTraversal::reachability(const ICFGNode *src, const ICFGNode *dst){
    std::pair<const ICFGNode*, CallStack> currentState = std::make_pair(src, callstack);

    if(visited.count(currentState)){
        return;
    }
 
    visited.insert(currentState);

    path.push_back(src->getId());

    if(src == dst){
        collectICFGPath(path);

    }

    for(const ICFGEdge *edge : src->getOutEdges()){

        if(const CallCFGEdge *callEdge = SVFUtil::dyn_cast<CallCFGEdge>(edge)){
            callstack.push_back(callEdge->getSrcNode());
            reachability(edge->getDstNode(), dst);
            callstack.pop_back();
        } 
        else if(const RetCFGEdge *retEdge = SVFUtil::dyn_cast<RetCFGEdge>(edge)){
            
            if(!callstack.empty() && callstack.back() == retEdge->getCallSite()){
                const ICFGNode *top = callstack.back();
                callstack.pop_back();
                reachability(edge->getDstNode(), dst);
                callstack.push_back(top);
            }
            else if (callstack.empty()){
                reachability(edge->getDstNode(), dst);

            }
        
        }
        else if (SVFUtil::dyn_cast<IntraCFGEdge>(edge)){
            reachability(edge->getDstNode(), dst);
        }
            
        
    }
    visited.erase(currentState);
    path.pop_back();

}

// There are hidden test cases up to 10 you can see 3, ensure to use cpp API keys for this
// Some test cases might have multiple paths, ensure to print all the paths in the format mentioned above
// Ensure you understand the Inter and Intra CFG node ensure you are traversing the ICFG and not CFG, you can use the API provided in the SVF framework to traverse the ICFG
// Ensure you use special handling strategies
// SVFUtil::dyn_cast - Use this cos it does not exit your code when running 