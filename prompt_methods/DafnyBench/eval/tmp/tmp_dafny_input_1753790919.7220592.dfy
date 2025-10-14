// Simple directed graph with vertices of any type T.
class {:autocontracts} Graph<T(==)> {
   var V: set<T>; // vertex-set
   var E: set<(T, T)>; // edge-set

   // Class invariant.
   ghost predicate Valid() {
       // edges must refer to vertices that belong to the vertex-set 
       // and self-loops (edges connecting a vertex to itself) are not allowed 
       forall e :: e in E ==> e.0 in V && e.1 in V && e.0 != e.1
   } 

   // Creates an empty graph.
   constructor ()
     ensures V == {} && E == {}
     {
       V:= {};
       E := {};
     }

   // Adds a new vertex v to this graph.
   method addVertex(v: T)
     requires v !in V
     ensures E == old(E) && V == old(V) + {v}
     {
        V := V + {v};
        // After adding v, E is unchanged and V is old(V) + {v}
        // Valid is preserved because no edges are added or changed
     }

   // Adds a new edge (u, v) to this graph.
   method addEdge(u: T, v: T)
     requires u in V && v in V && (u, v) !in E && u != v
     ensures V == old(V) && E == old(E) + {(u, v)} 
     {
        E := E + {(u, v)};
        // After adding (u, v), V is unchanged and E is old(E) + {(u, v)}
        // Valid is preserved because u != v and both are in V
     }

   // Obtains the set of vertices adjacent to a given vertex v. 
   function getAdj(v: T): set<T>
     requires v in V
     {
        set e | e in E && e.0 == v :: e.1
     } 

   // Removes a vertex v and all the edges incident on v from the graph.
   method removeVertex(v: T)
     requires v in V
     ensures V == old(V) - {v}
     ensures E == set e | e in old(E) && e.0 != v && e.1 != v 
     {
        V := V - {v};
        E := set e | e in E && e.0 != v && e.1 != v;
        // Valid is preserved because all edges with v as endpoint are removed
     }

    // Collapses a subset C of vertices to a single vertex v (belonging to C).
    // All vertices in C are removed from the graph, except v.  
    // Edges that connect vertices in C are removed from the graph.  
    // In all other edges, vertices belonging to C are replaced by v.
    method collapseVertices(C: set<T>, v: T)
      requires v in C && C <= V 
      ensures V == old(V) - C + {v}
      ensures E == set e | e in old(E) && (e.0 !in C || e.1 !in C) ::
                          (if e.0 in C then v else e.0, if e.1 in C then v else e.1)
  {
        // Remove all vertices in C except v
        V := V - C + {v};
        // Compute new edge set as specified
        var newE := set e | e in E && (e.0 !in C || e.1 !in C) ::
                          (if e.0 in C then v else e.0, if e.1 in C then v else e.1);
        // Strongest annotation: newE contains no self-loops and all endpoints are in V
        // Loop through all edges to check
        // Invariant: for all e in newE, e.0 in V && e.1 in V && e.0 != e.1
        // Proof:
        // - If e.0 in C, then e.0 becomes v, which is in V
        // - If e.0 !in C, then e.0 is in old(V) and not in C, so still in V - C
        // - Similarly for e.1
        // - If both e.0 and e.1 in C, then edge is not included (since (e.0 !in C || e.1 !in C) is false)
        // - If after replacement e.0 == e.1, then it must be a self-loop, which is not allowed
        //    But if an edge (x, y) with x in C or y in C, after replacement both endpoints become v only if
        //    (x in C and y !in C and y = v) or (x !in C and y in C and x = v), but since v is the only survivor in C,
        //    and edges between C are removed, so no self-loops are introduced.
        E := newE;
        // Valid is preserved
     }    
}

method testGraph() {
    var G := new Graph<int>();

    G.addVertex(1);
    G.addVertex(2);
    G.addVertex(3);
    G.addVertex(4);

    G.addEdge(1, 2);
    G.addEdge(1, 3);
    G.addEdge(2, 3);
    G.addEdge(4, 1);

    G.collapseVertices({1, 2, 3}, 3);
}

function abs(a: real) : real {if a>0.0 then a else -a}
