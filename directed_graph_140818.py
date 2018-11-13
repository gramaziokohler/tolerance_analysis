from compas.datastructures.network import Network
from compas_fab.fab.geometry import Frame, Transformation
from compas.geometry.elements import Line
from compas.geometry import distance_point_point
from collections import deque
import random as r
from graphviz import Digraph
from heap import Heap
import random
import operator
import itertools

r.seed(1)

__author__     = 'Augusto Gandia'
__copyright__  = 'Copyright 2018, Gramazio Kohler Research - ETH Zurich'
__license__    = 'MIT'
__email__      = 'gandia@arch.ethz.ch'

def setup(rawData):
        cities = list()
        #Create and return sorted data in list
        data = list() 

        for line in rawData:
            item = list()
            temp = line.split()
            item.extend([temp[0],temp[1],int(temp[2])])
            cities.extend([temp[0],temp[1]])
            data.append(item)
        return sorted(data, key=operator.itemgetter(2)),sorted(set(cities))
        
def depth_first_tree(adjacency, root):
    """Construct a spanning tree using a depth-first search.
    Parameters
    ----------
    adjacency : dict
        An adjacency dictionary.
    root : hashable
        The identifier of the root node.
    Returns
    -------
    list
        List of nodes in depth-first order.
    dict
        Dictionary of predecessors for each of the nodes.
    list
        The depth-first paths.
    """
    adjacency = {key: set(nbrs) for key, nbrs in iter(adjacency.items())}
    tovisit = [root]
    visited = set()
    ordering = []
    predecessors = {}
    paths = [[root]]
    #if there are nodes in tovisit
    while tovisit:
        # pop the last added element from the stack
        node = tovisit.pop()
        if node not in visited:
            # add node to last path
            paths[-1].append(node)
            # mark the node as visited
            visited.add(node)
            ordering.append(node)
            # add the unvisited nbrs to the stack
            nodes = adjacency [node] - visited
            # if there still not visited nbrs
            if nodes:
                for child in nodes:
                    predecessors[child] = node
            else:
                paths.append([])
            tovisit.extend(nodes)
    if not len(paths[-1]):
        del paths[-1]
    return ordering, predecessors, paths

def breadth_first_tree(adjacency, root):
    tovisit  = deque([root])
    visited  = set([root])
    ordering = [root]
    predecessors = {}
    paths = []
    while tovisit: 
        node = tovisit.popleft()
        for nbr in adjacency[node]:
            if nbr not in visited:
                predecessors[nbr]=node
                tovisit.append(nbr)
                visited.add(nbr)
                ordering.append(nbr)
        else:
            path = [node]
            while path[-1] in predecessors:
                path.append(predecessors[path[-1]])
            paths.append(list(reversed(path)))
    return ordering, predecessors, paths
def network_bfs_paths(adjacency, root, goal):
    """Return all paths from root to goal.

    Due to the nature of the search, the first path returned is the shortest.
    """
    adjacency = dict((key, set(nbrs)) for key, nbrs in adjacency.iteritems())
    tovisit = deque([(root, [root])])
    while tovisit:
        node, path = tovisit.popleft()
        for nbr in adjacency[node] - set(path):
            if nbr == goal:
                yield path + [nbr]
            else:
                tovisit.append((nbr, path + [nbr]))

def network_shortest_path(adjacency, root, goal):
    """"""
    try:
        return next(network_bfs_paths(adjacency, root, goal))
    except StopIteration:
        return None

def init(E):
    nodes = {}
    for e in E:
        nodes[e] = None
    return nodes

def find(nodes, U):
    if U not in nodes:
        print('Find failed: ' + str(U) + ' not found')
        return None
    if nodes[U] == None:
        return U
    return find(nodes,nodes[U])

def union(nodes,U0,U1):
    U1_temp = find(nodes,U1)
    U0_temp = find(nodes,U0)
    if U1_temp == None or U0_temp == None:
        failed = []
        if U0_temp == None:
            failed.append(U0)
        if U1_temp == None:
            failed.append(U1)
        print('\nUnion failed: Element(s) ' + str(failed) + ' not found\n')
        return None
    if U0_temp != U1_temp:
        nodes[U0_temp] = U1_temp
    return U1_temp

def check_connectivity(current_beam, adjacency, beams_geometry, result):
    #Type of beam (0 = bottom chord, 1 = top chord, 2 = verticals, 3 = wall rafter, 4 = slab rafter, 5 = diagonals)
    beams_type={0:0, 1:1, 2:2, 3:2, 4:4, 5:5, 6:3, 7:3, 8:3, 9:3, 10:3, 11:3, 12:3, 13:3, 14:5, 15:0, 16:1, 
    17:2, 18:4, 19:5, 20:3, 21:3, 22:3, 23:3, 24:3, 25:3, 26:5, 27:0, 28:1 ,29:2, 30:4, 31:5, 32:3, 33:3,
    34:3, 35:3, 36:3, 37:3, 38:0, 39:1 ,40:2 ,41:4, 42:3, 43:3, 44:3, 45:5, 46:0, 47:1, 48:2, 49:4, 50:5,
    51:3, 52:3, 53:3, 54:3, 55:5, 56:5, 57:3, 58:3, 59:3, 60:3, 61:5, 62:0, 63:1, 64:4, 65:5, 66:3, 67:3,
    68:3, 69:3, 70:5, 71:4, 72:4, 73:4, 74:4, 75:4, 76:4, 77:4, 78:4, 79:4, 80:4, 81:4, 82:4, 83:4, 84:4}
     
    check=False
    nbrs=set(adjacency[current_beam])
    #(0 = bottom chord) if beam is bottom chord it is fabricatable by default
    if beams_type[current_beam]==0:
        check=True

    #(1 = top chord) if beam is top cord check that at least four vertical neighbours are there
    if beams_type[current_beam]==1:
        #iter nbrs
        counter=0
        for nbr_node in set(nbrs):
            nbr_node_type=beams_type[nbr_node]
            #if nbr is vertical or diagonal
            if nbr_node_type==2:
                #check if any verticals or diagonal already assembled
                if str(nbr_node) in result:
                    counter=counter+1
        if counter>1:#it is considered to be stable if there is at least two supports
            check=True

    #(2 = verticals) if beam is vertical or diagonal check that at least one bottom_cord neighbour is assembled
    if beams_type[current_beam]==2:
        #iter nbrs
        for nbr_node in nbrs: 
            nbr_node_type=beams_type[nbr_node]
            #if nbr is bottom_cord 
            if nbr_node_type==0:
                #check if any bottom_cord already assembled
                if str(nbr_node) in result:
                    check=True

    #(3 = wall rafter) if beam is wall rafter
    if beams_type[current_beam]==3:
        #iter nbrs
        counter=0
        for nbr_node in nbrs:
            nbr_node_type=beams_type[nbr_node]
            #if nbr is bottom or top cord 
            if nbr_node_type==0 or nbr_node_type==1:
                #if already assembled
                if str(nbr_node) in result:
                    counter=counter+1
        if counter>1:
            check=True

    #(4 = slab rafter) if beam is slab rafter
    #To be true it needs to be connected to one top cord = 1 or to two slab rafter = 4
    if beams_type[current_beam]==4:
        #iter nbrs
        counter=0
        for nbr_node in nbrs:
            nbr_node_type=beams_type[nbr_node]
            #if nbr is top cord 
            if nbr_node_type==1:
                #if already assembled
                if str(nbr_node) in result:
                    counter=counter+2
            #if nbr is top cord
            if nbr_node_type==4:
                if str(nbr_node) in result:
                    counter=counter+1
        if counter>1:
            check=True

    #(3 = wall rafter) if beam is wall rafter
    if beams_type[current_beam]==5:
        #iter nbrs
        counter=0
        for nbr_node in nbrs:
            nbr_node_type=beams_type[nbr_node]
            #if nbr is bottom or top cord 
            if nbr_node_type==0 or nbr_node_type==2:
                #if already assembled
                if str(nbr_node) in result:
                    counter=counter+1
        if counter>1:
            check=True
    return check

# Method to perform Kruskal's Algorithm    
def kruskal(data,nodes,adjacency_dictionary,beams_geometry):
    distance = 0
    result = list()
    nodes = init(nodes)
    forward_counters={}
    beams_propagation_path={}
    stored_goal=[]
    predecessors=[]
    while len(data):
        weighted_edge = data.pop(0)
        if find(nodes,weighted_edge[0]) != find(nodes,weighted_edge[1]):
            if not check_connectivity(int(weighted_edge[0]), adjacency_dictionary, beams_geometry, result) or not check_connectivity(int(weighted_edge[1]), adjacency_dictionary, beams_geometry, result):
                key = '%s-%s' % (weighted_edge[0], weighted_edge[1])
                if key in forward_counters:
                    forward_counters[key] += 1
                else:
                    forward_counters[key] = 1
                forward_count=forward_counters[key]
                data.insert(forward_count, weighted_edge)
                continue
            forward_counters = {}
            union(nodes, weighted_edge[0],weighted_edge[1])
            beam_1=weighted_edge[0]
            beam_2=weighted_edge[1]
            result.append(beam_1)
            result.append(beam_2)
            #Store parent of each beam according to fabrication sequence
            #Remove duplicates from result
            seen = set()
            cleaned_result=[x for x in result if not (x in seen or seen.add(x))]
            #Build an adjacency dictionary for each assembly step
            beams_parent={}
            #Iterate already assembled beams
            for assembled_beam in cleaned_result:
                #Get current beam nbrs
                beam_nbrs=adjacency_dictionary[int(assembled_beam)]
                #Check if any assembled beam is neighbour of current beam
                for beam in cleaned_result:
                    if int(beam) in beam_nbrs:
                        #if key exists
                        if int(assembled_beam) not in beams_parent:
                            beams_parent.update({int(assembled_beam):[int(beam)]})
            """
            #shortest path for each beam
            root=int(cleaned_result[0])
            goal=int(cleaned_result[len(cleaned_result)-2])
            #if goal was not yet searched
            if goal not in stored_goal:
                stored_goal.append(goal)
                shortest_path=network_shortest_path(sequential_adjacency_dictionary,root,goal)
                beams_propagation_path.update({goal:shortest_path})
            root=int(cleaned_result[0])
            goal=int(cleaned_result[len(cleaned_result)-1])
            if goal not in stored_goal:
                stored_goal.append(goal)
                shortest_path=network_shortest_path(sequential_adjacency_dictionary,root,goal)
                beams_propagation_path.update({goal:shortest_path})
            """
    return cleaned_result, beams_parent

def midpoint_point_point(a, b):
    return [0.5 * (a[0] + b[0]),
            0.5 * (a[1] + b[1]),
            0.5 * (a[2] + b[2])]

def midpoint_line(line):
    return midpoint_point_point(*line)
    
def vertex_neighbours(self,key):
    """Return the neighbours of a vertex."""
    return list(self.halfedge[key])

def edge_connected_edges(self, u, v):
        edges = []
        for nbr in vertex_neighbours(self,u):
            if nbr in self.edge[u]:
                edges.append((u, nbr))
            else:
                edges.append((nbr, u))
        for nbr in vertex_neighbours(self,v):
            if nbr in self.edge[v]:
                edges.append((v, nbr))
            else:
                edges.append((nbr, v))
        return edges

def delete_vertex(self, key): #This could be removed in newer versions of compas
    for nbr in self.vertex_neighbours(key):
        del self.halfedge[key][nbr]
        del self.halfedge[nbr][key]
        if key in self.edge and nbr in self.edge[key]:
            del self.edge[key][nbr]
        else:
            del self.edge[nbr][key]
    del self.vertex[key]
    del self.halfedge[key]
    del self.edge[key]

class ToleranceNetwork(Network):
    #General Network required to 1) generate assembly sequence to 2) perform tolerance analysis
    def __init__(self, joint_edges, beam_edges, ordered_beams, weights_list):
        super(ToleranceNetwork, self).__init__() 
        input_dict = {'joint_edges': joint_edges, 'beam_edges': beam_edges, 'ordered_beams': ordered_beams}
        print "=======================================>"
        self.attributes.update(input_dict)
        self.build_geometry_network()
        self.build_topology_network (weights_list)
        self.assembly_sequence_search()
        self.build_tolerance_analysis_network()
        #self.assembly_sequence_draw()

    def build_geometry_network(self):
        #add vertices of beam_edges to Tolerance Network(vertices same as Geometry network)
        #iterate beam_edges indexes
        for index in range(len(self.attributes ['beam_edges'])):
            #get vertex coordinates 
            position = self.attributes['beam_edges'][index][0]
            #generate vertex u, add coordinates and vertex type as attribute
            u=self.add_vertex(attr_dict={'x': position[0], 'y' : position[1], 'z' : position[2], 'vertex_type': 'member'})
            #get vertex coordinates 
            position = self.attributes ['beam_edges'][index][1]
            #generate vertex v, add coordinates and vertex type as attribute
            v=self.add_vertex(attr_dict={'x': position[0], 'y' : position[1], 'z' : position[2], 'vertex_type': 'member'})
            #add beam edge, beam object, edge_type, u_coordinate , v_coordinate
            self.add_edge(u,v, {'edge_type': 'member','beam': self.attributes ['ordered_beams'][index], 'u_coordinate':self.vertex_coordinates(u), 'v_coordinate': self.vertex_coordinates(v), 'member_edge_nbrs': []})

        # BUILD GEOMETRY NETWORK
        #compare joint edges and beam edges
        store_joint_new_u=[]
        store_joint_new_v=[]
        #iterate joint edges
        for index in range (len(self.attributes['joint_edges'])):
            #get joint_vertices coordinates
            joint_u_coordinate=self.attributes ['joint_edges'][index][0] 
            joint_v_coordinate=self.attributes ['joint_edges'][index][1]
            #iterate beam edges
            corresponding_joint_u_index=None #this can be revised
            corresponding_joint_v_index=None
            for u,v,attr in self.edges(data=True):
                #get beam_vertices coordinates
                beam_u_coordinate=attr['u_coordinate']
                beam_v_coordinate=attr['v_coordinate']
                #compare joint vertex u and beam vertex u
                if distance_point_point(joint_u_coordinate,beam_u_coordinate) < 0.5:
                    global corresponding_joint_u_index
                    corresponding_joint_u_index=u
                #compare joint vertex u and beam vertex v
                elif distance_point_point(joint_u_coordinate,beam_v_coordinate) < 0.5:
                    global corresponding_joint_u_index
                    corresponding_joint_u_index=v
                #compare joint vertex v and beam vertex u
                elif distance_point_point(joint_v_coordinate,beam_u_coordinate) < 0.5:
                    global corresponding_joint_v_index
                    corresponding_joint_v_index=u
                #compare joint vertex v and beam vertex v
                elif distance_point_point(joint_v_coordinate,beam_v_coordinate) < 0.5:
                    global corresponding_joint_v_index
                    corresponding_joint_v_index=v
            #store corresponding joint v index
            store_joint_new_u.append(corresponding_joint_u_index)
            #store corresponding joint u index
            store_joint_new_v.append(corresponding_joint_v_index)
        for index in range(len(store_joint_new_v)):
            self.add_edge(store_joint_new_u[index], store_joint_new_v[index], {'edge_type': 'joint', 'beam': None})
        # STORE CONNECTIVITY IN EDGE MEMBERS
        #store connectivity in joint edges
        for u,v,attr in self.edges(data=True):
            if attr['edge_type']=='joint':
                connected_joint_edges_list=edge_connected_edges(self,u,v) #per beam edge a list of connected joint edges
                prev_list=[]
                #filter connected joint edges and store connected member edges
                for joint_edge in connected_joint_edges_list:
                    if self.get_edge_attribute(joint_edge[0],joint_edge[1],'edge_type')=='member':   
                        prev_list.append((joint_edge[0],joint_edge[1])) 
                #get existing neighbours from first edge
                first_edge_neighbours=self.get_edge_attribute(prev_list[0][0],prev_list[0][1],'member_edge_nbrs')
                first_edge_neighbours.append(prev_list[1])
                #get existing neighbours from second edge
                sec_edge_neighbours=self.get_edge_attribute(prev_list[1][0],prev_list[1][1],'member_edge_nbrs')
                sec_edge_neighbours.append(prev_list[0])

    # GENERATE ASSEMBLY SEQUENCE NETWORK (beams=nodes and connections=edges)
    def build_topology_network(self, weights_list):
        beams_geometry=self.attributes['ordered_beams']
        #this "topology network" is an inversion of the "geometry_network" by turning beams into vertices
        self.assembly_sequence_network=AssemblySequenceNetwork(self, weights_list, beams_geometry)

    def assembly_sequence_search(self):
        #Adjacency dictionary for COMPAS deph_first_tree
        adjacency_dictionary=self.assembly_sequence_network.adjacency_dictionary
        beams_geometry=self.assembly_sequence_network.beams_geometry
        #Create a list that represents the relations for a directed graph
        #List with weighted edges (a, b, c) a=start vertex b=end vertex c=weight
        directed_edges=[]
        #Iterate nodes
        for node in adjacency_dictionary:
            parent_weight = self.assembly_sequence_network.get_vertex_attribute(node, 'weight')
            #Iterate neighbours of each node
            for nbr in adjacency_dictionary[node]:
                child_weight = self.assembly_sequence_network.get_vertex_attribute(nbr, 'weight') 
                parent = [str(nbr), str(node), parent_weight]
                child = [str(node), str(nbr), child_weight]
                if parent_weight > child_weight:
                    directed_edges.append(parent)
                    if child in directed_edges:
                        directed_edges.remove(child)
                else:
                    directed_edges.append(child)
                    if parent in directed_edges:
                        directed_edges.remove(parent)
        sorted_directed_edges = sorted(directed_edges, key=operator.itemgetter(2))
        self.sorted_directed_edges = sorted_directed_edges[:]
        nodes = map(str, self.assembly_sequence_network.vertices())
        result, beams_parent = kruskal(sorted_directed_edges,nodes,adjacency_dictionary,beams_geometry)
        self.result=result
        self.beams_parent=beams_parent

    def assembly_sequence_draw(self):
        result=self.result
        weighted_edges=self.sorted_directed_edges
        #color convention
        color="/rdbu8/"
        #setup
        directed_graph=Digraph(format='png')
        directed_graph.attr(ranksep='7', resolution='80', lheight='1000', lwidth='2000', smoothing='true')#, bgcolor='transparent')
        root=result[0]
        #add Root
        directed_graph.node(root, fontsize='60', width='3', fixedsize='true', shape='circle', label='Beam '+str(root), style='filled', color=color+str(1))#label='beam '+str(root) #Brewer colors http://graphviz.org/doc/info/colors.html#brewer
        #add nodes and edges returned from assembly sequence
        for beams in result:
            weight=self.result_network.get_vertex_attribute(int(beams), 'weight')
            directed_graph.node(beams, fontsize='60', width='3', fixedsize='true', shape='circle', label='Beam '+str(beams), style='filled', color=color+str(weight))#, color='transparent')

        #for edge in weighted_edges:
            #directed_graph.edge(edge[0],edge[1], headlabel=str(edge[2]), labeldistance='6', fontsize='60', arrowsize='3')#, fontcolor=color+str(int(weight)))
        #render
        #directed_graph.render(filename = 'C:/Users/gandiaa/Documents/projects/tolerance_analysis/connectivity_graph', cleanup=True)

        """
        #setup
        directed_graph=Digraph(format='png')
        directed_graph.attr(ranksep='7', resolution='80', lheight='1000', lwidth='2000', smoothing='true')#, bgcolor='transparent')
        root=self.result[0]
        #add Root
        directed_graph.node(root, fontsize='60', width='3', fixedsize='true', shape='circle', label='Beam '+str(root), style='filled', color=color+str(1))#label='beam '+str(root) #Brewer colors http://graphviz.org/doc/info/colors.html#brewer
        #add nodes and edges returned from assembly sequence
        for n in self.result:
            weight=self.result_network.get_vertex_attribute(int(n), 'weight')
            directed_graph.node(n, fontsize='60', width='3', fixedsize='true', shape='circle', label='Beam '+str(n), style='filled', color=color+str(weight))#, color='transparent')

        weighted_edges=[self.result[int(i):int(i) + 3] for i in range(0, len(self.result), 3)]
        for e in weighted_edges:
            directed_graph.edge(e[0],e[1], headlabel=str(e[2]), labeldistance='6', fontsize='60', arrowsize='3')#, fontcolor=color+str(int(weight)))

        directed_graph.render(filename = 'C:/Users/gandiaa/Documents/projects/tolerance_analysis/connectivity_graph', cleanup=True)
        """
        """
        #adjacency_dictionary
        adjacency_dictionary=self.result_network.adjacency_dictionary
        #set root
        root=str(self.paths[0][0])
        #setup
        directed_graph=Digraph(format='png')#format='png')
        directed_graph.attr(ranksep='7', resolution='80', lheight='1000', lwidth='2000', smoothing='true', bgcolor='transparent')
        #color convention
        color="/rdbu8/"
        #add Root
        #directed_graph.node(root, fontsize='60', width='3', fixedsize='true', shape='circle', label='Beam '+str(root), style='filled', color=color+str(1))#label='beam '+str(root) #Brewer colors http://graphviz.org/doc/info/colors.html#brewer
        #add nodes and edges returned from breadth_first tree
        added_edges=[]
        for tree in self.paths:
            level=int(len(tree)-1)
            node=str(tree[level])
            color_by_weight=self.result_network.get_vertex_attribute(int(node), 'weight')
            directed_graph.node(node, fontsize='60', width='3', fixedsize='true', shape='circle', label='Beam '+str(node), style='filled', color='transparent')# color=color+str(color_by_weight))#width='0.5', fixedsize='true', label='beam '+str(node)#Brewer colors http://graphviz.org/doc/info/colors.html#brewer
            if len(tree) != 1:
                parent=str(tree[len(tree)-2])
                child=str(tree[len(tree)-1])
                i=self.paths.index(tree)-1
                weight=self.breadth_first_weighted_edges[i].split(' ')[2]
                directed_graph.edge(parent,child, headlabel=str(weight), labeldistance='6', fontsize='60', arrowsize='3')#, fontcolor=color+str(int(weight)))
                added_edges.append((parent,child))
        
        #add not selected edges
        for ordered_node in self.ordering:
            for connected_node in adjacency_dictionary[ordered_node]:
                ordered_node=str(ordered_node)
                connected_node=str(connected_node) 
                if (ordered_node,connected_node) not in added_edges and (connected_node,ordered_node) not in added_edges:
                    weight=self.result_network.get_vertex_attribute(int(connected_node), 'weight')
                    directed_graph.edge(ordered_node,connected_node,constraint='false', color='grey80')
                    added_edges.append((ordered_node,connected_node))
        
        counter=0
        for key in self.result:edge_beam
            #for node in list(directed_graph)[3:]:
            for node in directed_graph.body:
                key = str(key)
                if node.startswith('\t%s [' % key):
                    weight=self.result_network.get_vertex_attribute(int(key), 'weight')
                    index=directed_graph.body.index(node)
                    directed_graph.body[index]=directed_graph.body[index].replace('style=filled', 'style=filled,color="/rdbu8/'+str(weight)+'"')
                    #directed_graph.render(filename = 'C:/Users/gandiaa/Documents/projects/tolerance_analysis/connectivity_graph_'+str(counter), cleanup=True)     
                    counter+=1
        #render
        #directed_graph.render(filename = 'C:/Users/gandiaa/Documents/projects/tolerance_analysis/connectivity_graph', cleanup=True)
        """
    def build_tolerance_analysis_network(self):
        #1) Store connection frame in geometry network vertices
        for u,v,attr in self.edges(data=True):
            if attr['edge_type']=='member':
                #Rhino Plane
                end_plane_u=attr['beam'].end_planes[0]
                end_plane_v=attr['beam'].end_planes[1]
                #Compas Frame
                frame_u=Frame(end_plane_u[0], end_plane_u[1], end_plane_u[2])
                frame_v=Frame(end_plane_v[0], end_plane_v[1], end_plane_v[2])
                #Set Compas Frame as attribute
                self.set_edge_attribute(u,v,'connection_frames', (frame_u, frame_v))
        #2) Propagate tolerances

        beams_parent=self.beams_parent

        #self.tolerance_analysis_network = ToleranceAnalysisNetwork(self, beams_geometry)
"""
#Network to perform tolerance analysis
class ToleranceAnalysisNetwork(Network):
    def __init__(self,  geometry_network, beams_geometry):
        super(ToleranceAnalysisNetwork, self).__init__() 
        input_dict = {'edges': geometry_network.edges(data=True)}
        self.attributes.update(input_dict)
        self.build_network(beams_geometry)

    def build_network(self,beams_geometry):
        #Iterate geometry network member edges
        for u,v,attr in self.attributes['edges']:
            if attr['edge_type']=='member':
                print u, v, attr
                print beams_geometry[u/2].end_planes
"""

#Network to generate assembly sequence
class AssemblySequenceNetwork (Network):
    def __init__(self, geometry_network, weights_list, beams_geometry):
        super(AssemblySequenceNetwork, self).__init__() 
        input_dict = {'edges': geometry_network.edges(data=True)}
        self.attributes.update(input_dict)
        self.beams_geometry=beams_geometry
        self.invert_network(weights_list)

    def invert_network (self, weights_list):
        #to translate from member being an edge to member being a vertex 
        #only the u value of each member is used and divided by 2.
        #thus it turns from being (u=0,u=2,u=4...) to (u=0,u=1,u=2...) 
        #iter member edges of geometry network
        for u,v,attr in self.attributes['edges']:
            if attr['edge_type']=='member':
                #get midpoint for each member edge of geometry network
                beam_edge_mid=midpoint_line((attr['u_coordinate'],attr['v_coordinate']))
                #create new vertex and use as coordinate the midpoint of u and v
                self.add_vertex(attr_dict={'x': beam_edge_mid[0], 'y' : beam_edge_mid[1], 'z' : beam_edge_mid[2]})#add beam_vertex
        #create adjacency dictionary
        adjacency_dict={}
        for u,v,attr in self.attributes['edges']:
            if attr['edge_type']=='member':
                temp_connected_vertex=[]
                #iter connected member edges of geometry network
                for connected_vertices in attr['member_edge_nbrs']:
                    #store connected member as its u value divided by 2 
                    temp_connected_vertex.append(connected_vertices[0]/2)
                adjacency_dict[u/2]=temp_connected_vertex
        #prepare adjacency dictionary for COMPAS traverse
        self.adjacency_dictionary=adjacency_dict
        #add adjacency and weight attribute to vertices
        for u, attr in self.vertices(data=True):
            self.set_vertex_attribute(u,'weight', weights_list[u])
            self.set_vertex_attribute(u,'connected_vertices', adjacency_dict[u])

if __name__ == "__main__":
    temp_frames_array = [] 
