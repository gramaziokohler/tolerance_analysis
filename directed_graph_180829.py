from compas.datastructures.network import Network
from compas_fab.fab.geometry import Frame, Transformation, Translation, Rotation
from compas.geometry.elements import Line
from compas.geometry import distance_point_point
from collections import deque
import random as r
from graphviz import Digraph
from heap import Heap
import random
import operator
import itertools
import math


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
    #Type of beam (0 = bottom chord, 1 = top chord, 2 = verticals, 3 = wall infill, 4 = slab rafter, 5 = diagonals)
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

    #(1 = top chord) if beam is top cord check that at least two vertical neighbours are there
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
        counter=0
        #iter nbrs
        for nbr_node in nbrs: 
            nbr_node_type=beams_type[nbr_node]
            #if nbr is bottom_cord 
            if nbr_node_type==0:
                #check if any bottom_cord already assembled
                if str(nbr_node) in result:
                    counter=counter+1
                    
        for beam_index in result:
            beam_type=beams_type[int(beam_index)]
            if beam_type==0:
                counter=counter+1
        if counter>10:
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
        for beam_index in result:
            beam_type=beams_type[int(beam_index)]
            if beam_type==4:
                counter=counter+1
        if counter>10:
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
        #check if diagonals are already assembled

        for beam_index in result:
            beam_type=beams_type[int(beam_index)]
            if beam_type==4:
                counter=counter+1
        if counter>7:
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
        self.attributes.update(input_dict)
        self.build_geometry_network()
        self.build_topology_network (weights_list)
        self.assembly_sequence_search()
        self.build_tolerance_analysis_network()

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
        #iterate edges
        for u,v,attr in self.edges(data=True):
            #filter joint edges
            if attr['edge_type']=='joint':
                #edges connected to joint edge
                connected_edges=edge_connected_edges(self,u,v) 
                connected_member_edges=[]
                #filter connected member edges and store connected member edges
                for connected_edge in connected_edges:
                    #if edge is beam edge
                    if self.get_edge_attribute(connected_edge[0],connected_edge[1],'edge_type')=='member':
                        #store it (two members per joint)   
                        connected_member_edges.append((connected_edge[0],connected_edge[1])) 
                #get existing neighbours from first edge
                first_member_edge_neighbours=self.get_edge_attribute(connected_member_edges[0][0],connected_member_edges[0][1],'member_edge_nbrs')
                #(by appending them they get included in the attribute)
                first_member_edge_neighbours.append(connected_member_edges[1]) 
                #get existing neighbours from second edge 
                sec_member_edge_neighbours=self.get_edge_attribute(connected_member_edges[1][0],connected_member_edges[1][1],'member_edge_nbrs')
                #(by appending them they get included in the attribute)
                sec_member_edge_neighbours.append(connected_member_edges[0])

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

    def build_tolerance_analysis_network(self):
        result=self.result
        beams_parent=self.beams_parent

        def translate_frame_own_xyz(transformation,x_dist, y_dist, z_dist):
            x_transform = [[1, 0, 0, (transformation[0, 0] * x_dist)],
                           [0, 1, 0, (transformation[1, 0] * x_dist)],
                           [0, 0, 1, (transformation[2, 0] * x_dist)],
                           [0, 0, 0, 1]]
            y_transform = [[1, 0, 0, (transformation[0, 1]*y_dist)],
                           [0, 1, 0, (transformation[1, 1]*y_dist)],
                           [0, 0, 1, (transformation[2, 1]*y_dist)],
                           [0, 0, 0, 1]]
            z_transform = [[1, 0, 0, (transformation[0, 2]*z_dist)],
                           [0, 1, 0, (transformation[1, 2]*z_dist)],
                           [0, 0, 1, (transformation[2, 2]*z_dist)],
                           [0, 0, 0, 0]]
            return Translation.from_matrix(z_transform)*Translation.from_matrix(y_transform)*Translation.from_matrix(x_transform)
        
        def get_middle_frame(beam):
            middle_frame=Frame(beam.frame[0],beam.frame[1],beam.frame[2])
            middle_frame_transform=Transformation.from_frame(middle_frame)
            middle_frame_inv_transform=Transformation.from_frame(middle_frame).inverse()
            middle_frame.transform(middle_frame_inv_transform)
            fix_middle_rot_x=Rotation.from_axis_and_angle(origin_frame.xaxis,math.radians(180))
            fix_middle_rot_y=Rotation.from_axis_and_angle(origin_frame.yaxis,math.radians(-90))
            middle_frame.transform(fix_middle_rot_x)
            middle_frame.transform(fix_middle_rot_y)
            middle_frame.transform(middle_frame_transform)
            return middle_frame

        def get_child_and_parent_data (beam_nr_assembly_sequence):

            """
            ///Geometry Network or GN (member and joint members)
            attr=
            'member_edge_nbrs':[(8, 9), (32, 33)], 
            'connection_frames', 
            'u_coordinate', 'v_coordinate',
            'edge_type': 'member' or 'joint', 
            'beam'

            Example:
            for u,v,attr in self.edges(data=True):
                print "Geometry Network u,v,att", u,v,attr
            
            ///Topology network or TN (member as vertex)

            attr=
            'x','y','z', 
            'connected_vertices':[0, 2], 
            'weight': 2

            Example:
            for u,attr in self.topology_network.vertices(data=True):
                print "Topology Network u,v,att", u,v,attr

            Mapping between networks:
            Geometry network (edge_u,edge_v) to Topology Network (vertex)
            vertex (Beam) = edge_u/2 (Connection)

            Beam of Topology Network (vertex) to Beam of Geometry network
            edge_u=vertex*2
            edge_v=(vertex*2)+1
            """

            child_beam_index_TN=int(result[beam_nr_assembly_sequence])
            parent_beam_index_TN=beams_parent[child_beam_index_TN][0]
            #Get child vertices index in GN
            beam_u_GN=child_beam_index_TN*2
            beam_v_GN=child_beam_index_TN*2+1 
            ch_beam=self.get_edge_attribute(beam_u_GN,beam_v_GN,'beam')
            #Get parent vertices index in GN
            p_beam_u_GN=parent_beam_index_TN*2
            p_beam_v_GN=parent_beam_index_TN*2+1
            p_beam=self.get_edge_attribute(p_beam_u_GN,p_beam_v_GN,'beam')
            child_to_parent_joint=[]
            #iterate joint edges in GN and find combination of parent and child vertex that matches
            for u,v,attr in self.edges(data=True):
                if attr['edge_type']=='joint':
                    # child u 
                    if (beam_u_GN,p_beam_u_GN)==(u,v):
                        child_to_parent_joint.append(u)
                        child_to_parent_joint.append(v)
                    elif (beam_u_GN,p_beam_u_GN)==(v,u):
                        child_to_parent_joint.append(v)
                        child_to_parent_joint.append(u)
                    elif (beam_u_GN,p_beam_v_GN)==(u,v):
                        child_to_parent_joint.append(u)
                        child_to_parent_joint.append(v)
                    elif (beam_u_GN,p_beam_v_GN)==(v,u):
                        child_to_parent_joint.append(v)
                        child_to_parent_joint.append(u)
                    elif (beam_v_GN,p_beam_u_GN)==(u,v):
                        child_to_parent_joint.append(u)
                        child_to_parent_joint.append(v)
                    elif (beam_v_GN,p_beam_u_GN)==(v,u):
                        child_to_parent_joint.append(v)
                        child_to_parent_joint.append(u)
                    elif (beam_v_GN,p_beam_v_GN)==(u,v):
                        child_to_parent_joint.append(u)
                        child_to_parent_joint.append(v)
                    elif (beam_v_GN,p_beam_v_GN)==(v,u):
                        child_to_parent_joint.append(v)
                        child_to_parent_joint.append(u)
            
            # joint vertices indices (GN)
            child_joint_vertex=child_to_parent_joint[0]
            parent_joint_vertex=child_to_parent_joint[1]

            if parent_joint_vertex==p_beam_u_GN:
                parent_other_vertex=p_beam_v_GN
            else:
                parent_other_vertex=p_beam_u_GN
            if child_joint_vertex==beam_u_GN:
                child_other_vertex=beam_v_GN
            else:
                child_other_vertex=beam_u_GN

            #Get child and parent beam
            p_beam_mesh=self.get_edge_attribute(parent_other_vertex,parent_joint_vertex,'beam')
            ch_beam_mesh=self.get_edge_attribute(child_other_vertex,child_joint_vertex,'beam')
            #Get parent unorganized planes
            p_beam_frame_0=p_beam_mesh.end_planes[0]
            p_beam_frame_0_compas=Frame(p_beam_frame_0.Origin, p_beam_frame_0.XAxis, p_beam_frame_0.YAxis)
            p_beam_frame_1=p_beam_mesh.end_planes[1]
            p_beam_frame_1_compas=Frame(p_beam_frame_1.Origin, p_beam_frame_1.XAxis, p_beam_frame_1.YAxis)
            #Get child unorganized planes
            ch_beam_frame_0=ch_beam_mesh.end_planes[0]
            ch_beam_frame_0_compas=Frame(ch_beam_frame_0.Origin, ch_beam_frame_0.XAxis, ch_beam_frame_0.YAxis)
            ch_beam_frame_1=ch_beam_mesh.end_planes[1]
            ch_beam_frame_1_compas=Frame(ch_beam_frame_1.Origin, ch_beam_frame_1.XAxis, ch_beam_frame_1.YAxis)
            #Get parent vertex origin
            parent_other_vertex_pt=(self.get_vertex_attribute(parent_other_vertex, 'x'),self.get_vertex_attribute(parent_other_vertex, 'y'),self.get_vertex_attribute(parent_other_vertex, 'z'))
            parent_joint_vertex_pt=(self.get_vertex_attribute(parent_joint_vertex, 'x'),self.get_vertex_attribute(parent_joint_vertex, 'y'),self.get_vertex_attribute(parent_joint_vertex, 'z'))
            #Get child vertex origin
            child_other_vertex_pt=(self.get_vertex_attribute(child_other_vertex, 'x'),self.get_vertex_attribute(child_other_vertex, 'y'),self.get_vertex_attribute(child_other_vertex, 'z'))
            child_joint_vertex_pt=(self.get_vertex_attribute(child_joint_vertex, 'x'),self.get_vertex_attribute(child_joint_vertex, 'y'),self.get_vertex_attribute(child_joint_vertex, 'z'))
            
            #Compare parent frame 0 with coordinates of parent other vertex and parent other joint and store frame 
            if distance_point_point(p_beam_frame_0.Origin,parent_other_vertex_pt) < 200:
                self.set_vertex_attribute(parent_other_vertex, 'connection_frame', p_beam_frame_0_compas)
                self.set_vertex_attribute(parent_joint_vertex, 'connection_frame', p_beam_frame_1_compas)
            if distance_point_point(p_beam_frame_0.Origin,parent_joint_vertex_pt) < 200:
                self.set_vertex_attribute(parent_other_vertex, 'connection_frame', p_beam_frame_1_compas)
                self.set_vertex_attribute(parent_joint_vertex, 'connection_frame', p_beam_frame_0_compas)

            if distance_point_point(ch_beam_frame_0.Origin,child_other_vertex_pt) < 200:
                self.set_vertex_attribute(child_other_vertex, 'connection_frame', ch_beam_frame_0_compas)
                self.set_vertex_attribute(child_joint_vertex, 'connection_frame', ch_beam_frame_1_compas)
            if distance_point_point(ch_beam_frame_0.Origin,child_joint_vertex_pt) < 200:
                self.set_vertex_attribute(child_other_vertex, 'connection_frame', ch_beam_frame_1_compas)
                self.set_vertex_attribute(child_joint_vertex, 'connection_frame', ch_beam_frame_0_compas)
            
            # joint frames
            parent_joint=self.get_vertex_attribute(parent_joint_vertex, 'connection_frame')
            parent_end=self.get_vertex_attribute(parent_other_vertex, 'connection_frame')
            child_joint=self.get_vertex_attribute(child_joint_vertex, 'connection_frame')
            child_end=self.get_vertex_attribute(child_other_vertex, 'connection_frame')

            return p_beam, ch_beam, parent_end, parent_joint, child_joint, child_end, parent_other_vertex, parent_joint_vertex, child_joint_vertex, child_other_vertex
 
        """Parameters --> here generated tolerances will be plugged""" 
        cuts_tolerance=1
        axial_tolerance=1

        #3) Concatenate transformations of parent and child

        #Inputs

        #cuts_tolerance (value)
        #axial_tolerance (value)
        #p_beam (frame)
        #ch_beam (frame)
        #parent_end (frame)
        #parent_joint (frame)
        #child_joint (frame)
        #child_other (frame)

        #Outputs tbd
        #
        #
        #
        
        #2) Get child and parent beams, frames and accumulated tolerances
        p_beam, ch_beam, parent_end, parent_joint, child_joint, child_end, parent_other_vertex, parent_joint_vertex, child_joint_vertex, child_other_vertex = get_child_and_parent_data(1)

        #Transformations
        transformations=[]

        #Beam 0 - Start postion
        origin_frame=Frame([0, 0, 0], [1, 0, 0], [0, 1, 0])
        T_origin=Transformation.from_frame_to_frame(origin_frame,parent_end)
        transformations.append(T_origin)
        #Beam 0 - Face 0 with cut tolerance
        F0=Frame(parent_end.point, parent_end.xaxis, parent_end.yaxis)
        F0=F0.transform(T_origin.inverse())
        cut_rot=Rotation.from_axis_and_angle(origin_frame.xaxis,math.radians(cuts_tolerance))
        F0.transform(cut_rot)
        F0.transform(T_origin)
        T0=Transformation.from_frame_to_frame(parent_end,F0)        
        transformations.append(T0*T_origin)
        #Store cut tolerance in vertex
        self.set_vertex_attribute(parent_other_vertex, 'tolerance', T0*T_origin)#wierd, its and exception
        #Beam 0 - Middle
        middle_frame=get_middle_frame(p_beam)
        FM=Frame(middle_frame.point, middle_frame.xaxis, middle_frame.yaxis)
        FM=FM.transform(Transformation.from_frame(parent_end).inverse())
        half_axis_deformation=Rotation.from_axis_and_angle(origin_frame.xaxis,math.radians(axial_tolerance/3))
        FM.transform(half_axis_deformation)
        FM.transform(Transformation.from_frame(parent_end))
        TM=Transformation.from_frame_to_frame(parent_end,FM)
        transformations.append(T0*TM*T_origin)
        #Beam 0 - Face 1 with axis deviation
        F1=Frame(parent_joint.point, parent_joint.xaxis, parent_joint.yaxis)
        F1=F1.transform(Transformation.from_frame(middle_frame).inverse())
        axis_deformation=Rotation.from_axis_and_angle(origin_frame.xaxis,math.radians(axial_tolerance))
        F1.transform(axis_deformation)
        F1.transform(Transformation.from_frame(middle_frame))
        T1=Transformation.from_frame_to_frame(F0,F1)
        transformations.append(T0*T1*T_origin)
        #Beam 0 - Face 1 with cut tolerance
        F2=Frame(F1.point, F1.xaxis, F1.yaxis)
        F2=F2.transform(Transformation.from_frame(F1).inverse())
        F2.transform(cut_rot)
        F2.transform(Transformation.from_frame(F1))
        T2=Transformation.from_frame_to_frame(F1,F2)
        transformations.append(T0*T2*T1*T_origin)
        #Store cut tolerance in vertex
        self.set_vertex_attribute(parent_joint_vertex, 'tolerance', T0*T2*T1*T_origin)#wierd, its and exception
        
        """
        TODO
        Store tolerance
        example: Beam 0
                 Tolerance Face 0 = frame with cut (F0)
                 Tolerance Face 1 = frame with 2 cuts and axial deviation (F2)
        """
        
        p_beam, ch_beam, parent_end, parent_joint, child_joint, child_end, parent_other_vertex, parent_joint_vertex, child_joint_vertex, child_other_vertex = get_child_and_parent_data(2)  

        #(!)Transformation to interface missing
        acc_tolerance=self.get_vertex_attribute(parent_joint_vertex, 'tolerance')
        FI=Frame.from_transformation(T0*T_origin)#<===replace with acc_tolerance
        TI=Transformation.from_frame_to_frame(parent_joint, FI)
        #Transformation to parent joint
        T_origin_3=Transformation.from_frame_to_frame(origin_frame,parent_joint)
        transformations.append(TI*T_origin_3)
        
        #Transformation with cut tolerance
        F0_3=Frame(parent_end.point, parent_end.xaxis, parent_end.yaxis)
        F0_3=F0_3.transform(T_origin_3.inverse())
        cut_rot=Rotation.from_axis_and_angle(origin_frame.xaxis,math.radians(cuts_tolerance))
        F0_3.transform(cut_rot)
        F0_3.transform(T_origin_3)
        T0_3=Transformation.from_frame_to_frame(parent_end,F0_3)
        transformations.append(TI*T0_3*T_origin_3)
        #Store cut tolerance in vertex (just in case)
        self.set_vertex_attribute(child_joint_vertex, 'tolerance', TI*T0_3*T_origin_3)

        #Transformation to middle
        middle_frame_3=get_middle_frame(ch_beam)
        FM_3=Frame(middle_frame_3.point, middle_frame_3.xaxis, middle_frame_3.yaxis)
        FM_3=FM_3.transform(Transformation.from_frame(child_joint).inverse())
        FM_3.transform(half_axis_deformation)
        FM_3.transform(Transformation.from_frame(child_joint))
        TM_3=Transformation.from_frame_to_frame(child_joint,FM_3)
        transformations.append(TI*T0_3*TM_3*T_origin_3)

        #Transformation to axis deviation
        F1_3=Frame(child_end.point, child_end.xaxis, child_end.yaxis)
        F1_3=F1_3.transform(Transformation.from_frame(middle_frame_3).inverse())
        F1_3.transform(axis_deformation)
        F1_3.transform(Transformation.from_frame(middle_frame_3))
        T1_3=Transformation.from_frame_to_frame(child_joint,F1_3)
        transformations.append(TI*T0_3*T1_3*T_origin_3)

        #Transformation with cut tolerance
        F2_3=Frame(F1_3.point, F1_3.xaxis, F1_3.yaxis)
        F2_3=F2_3.transform(Transformation.from_frame(F1_3).inverse())
        F2_3.transform(cut_rot)
        F2_3.transform(Transformation.from_frame(F1_3))
        T2_3=Transformation.from_frame_to_frame(F1_3,F2_3)
        #TODO Store transformation in vertex (child_end_index)
        transformations.append(TI*T0_3*T2_3*T1_3*T_origin_3)
        #Store cut tolerance in vertex
        self.set_vertex_attribute(child_other_vertex, 'tolerance', TI*T0_3*T2_3*T1_3*T_origin_3)

        #Beam 2
        
        p_beam, ch_beam, parent_end, parent_joint, child_joint, child_end, parent_other_vertex, parent_joint_vertex, child_joint_vertex, child_other_vertex = get_child_and_parent_data(3)  

        self.parent_end=parent_end
        self.parent_joint=parent_joint
        self.child_joint=child_joint
        self.child_end=child_end

        #Transformation to parent joint
        T_origin_4=Transformation.from_frame_to_frame(origin_frame,parent_joint) 
        #Get tolerance of parent joint
        acc_tolerance_1=self.get_vertex_attribute(parent_joint_vertex, 'tolerance')
        #Frame to accumulated tolerance
        FI_4=Frame.from_transformation(TI*T0_3*T_origin_3)#replace later with tolerance
        #Transformation from parent joint to parent cut tolerance
        TI_4=Transformation.from_frame_to_frame(parent_joint, FI_4)
        transformations.append(TI_4*T_origin_4)
        TI_5=Transformation.from_frame_to_frame(parent_joint, child_joint)
        transformations.append(TI_4*TI_5*T_origin_4)

        #Transformation with cut tolerance
        F0_4=Frame(parent_joint.point, parent_joint.xaxis, parent_joint.yaxis) #why it was parent end in previous case????

        F0_4=F0_4.transform(T_origin_4.inverse())
        cut_rot=Rotation.from_axis_and_angle(origin_frame.xaxis,math.radians(cuts_tolerance))
        F0_4.transform(cut_rot)
        F0_4.transform(T_origin_4)
        T0_4=Transformation.from_frame_to_frame(parent_joint,F0_4) #why it was parent end in previous case????
        transformations.append(TI_4*TI_5*T0_4*T_origin_4)
        #Store cut tolerance in vertex (just in case)
        self.set_vertex_attribute(child_joint_vertex, 'tolerance', TI_4*TI_5*T0_4*T_origin_4)
        
        #Transformation to middle
        middle_frame_4=get_middle_frame(ch_beam)
        FM_4=Frame(middle_frame_4.point, middle_frame_4.xaxis, middle_frame_4.yaxis)
        FM_4=FM_4.transform(Transformation.from_frame(child_joint).inverse())
        FM_4.transform(half_axis_deformation)
        FM_4.transform(Transformation.from_frame(child_joint))
        TM_4=Transformation.from_frame_to_frame(child_joint,FM_4)
        transformations.append(TI_4*TM_4*TI_5*T0_4*T_origin_4)

        #Transformation to axis deviation
        F1_4=Frame(child_end.point, child_end.xaxis, child_end.yaxis)
        F1_4=F1_4.transform(Transformation.from_frame(middle_frame_4).inverse())
        F1_4.transform(axis_deformation)
        F1_4.transform(Transformation.from_frame(middle_frame_4))
        self.F1_4=F1_4
        T1_4=Transformation.from_frame_to_frame(child_joint,F1_4)
        transformations.append(TI_4*T1_4*TI_5*T0_4*T_origin_4)

        """
        #Transformation with cut tolerance
        F2_4=Frame(F1_4.point, F1_4.xaxis, F1_4.yaxis)
        F2_4=F2_4.transform(Transformation.from_frame(F1_4).inverse())
        F2_4.transform(cut_rot)
        F2_4.transform(Transformation.from_frame(F1_4))
        T2_4=Transformation.from_frame_to_frame(F1_4,F2_4)
        #TODO Store transformation in vertex (child_end_index)
        transformations.append(TI_4*T0_4*T2_4*T1_4*T_origin_4)
        #Store cut tolerance in vertex
        self.set_vertex_attribute(child_other_vertex, 'tolerance', TI_4*T0_4*T2_4*T1_4*T_origin_4)
        """
        self.transformations=transformations
        
        """
        #Display deformations
        displayed_deformations=[]
        pt_0_frame=Frame.from_transformation(transformations[0])
        pt_1_frame=Frame.from_transformation(transformations[2])
        line_0=Line((pt_0_frame.point[0],pt_0_frame.point[1],pt_0_frame.point[2]),(pt_1_frame.point[0],pt_1_frame.point[1],pt_1_frame.point[2]))
        displayed_deformations.append(line_0)
        pt_2_frame=Frame.from_transformation(transformations[2])
        pt_3_frame=Frame.from_transformation(transformations[3])
        line_1=Line((pt_2_frame.point[0],pt_2_frame.point[1],pt_2_frame.point[2]),(pt_3_frame.point[0],pt_3_frame.point[1],pt_3_frame.point[2]))
        displayed_deformations.append(line_1)
        pt_4_frame=Frame.from_transformation(transformations[6])
        pt_5_frame=Frame.from_transformation(transformations[7])
        line_2=Line((pt_4_frame.point[0],pt_4_frame.point[1],pt_4_frame.point[2]),(pt_5_frame.point[0],pt_5_frame.point[1],pt_5_frame.point[2]))
        displayed_deformations.append(line_2)
        pt_6_frame=Frame.from_transformation(transformations[7])
        pt_7_frame=Frame.from_transformation(transformations[8])
        line_3=Line((pt_6_frame.point[0],pt_6_frame.point[1],pt_6_frame.point[2]),(pt_7_frame.point[0],pt_7_frame.point[1],pt_7_frame.point[2]))
        displayed_deformations.append(line_3)
        pt_8_frame=Frame.from_transformation(transformations[9])
        pt_9_frame=Frame.from_transformation(transformations[10])
        line_4=Line((pt_8_frame.point[0],pt_8_frame.point[1],pt_8_frame.point[2]),(pt_9_frame.point[0],pt_9_frame.point[1],pt_9_frame.point[2]))
        displayed_deformations.append(line_4)
        pt_10_frame=Frame.from_transformation(transformations[10])
        pt_11_frame=Frame.from_transformation(transformations[12])
        line_5=Line((pt_10_frame.point[0],pt_10_frame.point[1],pt_10_frame.point[2]),(pt_11_frame.point[0],pt_11_frame.point[1],pt_11_frame.point[2]))
        displayed_deformations.append(line_5)
        
        self.displayed_deformations=displayed_deformations
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
