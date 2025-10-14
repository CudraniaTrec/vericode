
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
       assert V == {};
       assert E == {};
     }

   // Adds a new vertex v to this graph.
   method addVertex(v: T)
     requires v !in V
     ensures E == old(E) && V == old(V) + {v}
     {
        assert v !in V;
        var oldV := V;
        var oldE := E;
        V := V + {v};
        assert V == oldV + {v};
        assert E == oldE;
     }

   // Adds a new edge (u, v) to this graph.
   method addEdge(u: T, v: T)
     requires u in V && v in V && (u, v) !in E && u != v
     ensures V == old(V) && E == old(E) + {(u, v)} 
     {
        assert u in V && v in V && (u, v) !in E && u != v;
        var oldV := V;
        var oldE := E;
        E := E + {(u, v)};
        assert V == oldV;
        assert E == oldE + {(u, v)};
        assert forall e :: e in E ==> e.0 in V && e.1 in V && e.0 != e.1;
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
        assert v in V;
        var oldV := V;
        var oldE := E;
        V := V - {v};
        assert V == oldV - {v};
        // Remove all edges incident to v
        E := set e | e in E && e.0 != v && e.1 != v;
        assert E == set e | e in oldE && e.0 != v && e.1 != v;
        assert forall e :: e in E ==> e.0 in V && e.1 in V && e.0 != e.1;
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
        assert v in C && C <= V;
        var oldV := V;
        var oldE := E;
        V := V - C + {v};
        assert V == oldV - C + {v};
        // Compute new edge set
        var newE := set e | e in E && (e.0 !in C || e.1 !in C) ::
                          (if e.0 in C then v else e.0, if e.1 in C then v else e.1);
        // Loop invariant: all edges in newE refer to vertices in V and are not self-loops
        E := newE;
        assert E == set e | e in oldE && (e.0 !in C || e.1 !in C) ::
                          (if e.0 in C then v else e.0, if e.1 in C then v else e.1);
        assert forall e :: e in E ==> e.0 in V && e.1 in V && e.0 != e.1;
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
