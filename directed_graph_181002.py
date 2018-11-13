from compas.datastructures.network import Network
from compas_fab.fab.geometry import Frame, Transformation, Translation, Rotation
from compas.geometry.elements import Line
from compas.geometry import distance_point_point
from compas.geometry import project_point_plane
from compas.geometry import intersection_line_plane
from collections import deque
import random as r
from graphviz import Digraph
from heap import Heap
import random
import operator
import itertools
import math
from compas.geometry.elements import Vector, Line
import Rhino.Geometry as rg
import rhinoscriptsyntax as rs

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
    #0 = bottom chord
    if beams_type[current_beam]==0:
        check=True

    #1 = top chord
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

    #2 = verticals
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

    #3 = wall infill
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

    #4 = slab rafter
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

    #5 = diagonals
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
        if counter>8:
            check=True
    return check

# Method to perform Kruskal's Algorithm    
def kruskal(data,nodes,adjacency_dictionary,beams_geometry):
    distance = 0
    result = list()
    nodes = init(nodes)
    forward_counters={}
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

def get_vertices_index_GN(vertex_TN):
    vert_u=int(vertex_TN)*2
    vert_v=int(vertex_TN)*2+1
    return vert_u,vert_v

def get_deformed_beam_mesh(network, vert_u, vert_v):
    beam_mesh=network.get_edge_attribute(vert_u,vert_v,'deformed_beam') 
    return beam_mesh

def get_parent_child_joint_vertices(network, p_beam_u_GN, p_beam_v_GN, beam_u_GN, beam_v_GN):
    child_to_parent_joint=[]
    #iterate joint edges in GN and find combination of parent and child vertex that matches
    for u,v,attr in network.edges(data=True):
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

    return parent_other_vertex, parent_joint_vertex, child_other_vertex, child_joint_vertex

def get_beam_mesh(network, vert_u, vert_v, beam_type):
    mesh=network.get_edge_attribute(vert_u,vert_v,beam_type)
    return mesh

def get_parent_child_frames(network, p_beam_mesh,ch_beam_mesh, parent_other_vertex, parent_joint_vertex, child_other_vertex, child_joint_vertex):
    #Get child and parent beam
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
    parent_other_vertex_pt=(network.get_vertex_attribute(parent_other_vertex, 'x'),network.get_vertex_attribute(parent_other_vertex, 'y'),network.get_vertex_attribute(parent_other_vertex, 'z'))
    parent_joint_vertex_pt=(network.get_vertex_attribute(parent_joint_vertex, 'x'),network.get_vertex_attribute(parent_joint_vertex, 'y'),network.get_vertex_attribute(parent_joint_vertex, 'z'))
    #Get child vertex origin
    child_other_vertex_pt=(network.get_vertex_attribute(child_other_vertex, 'x'),network.get_vertex_attribute(child_other_vertex, 'y'),network.get_vertex_attribute(child_other_vertex, 'z'))
    child_joint_vertex_pt=(network.get_vertex_attribute(child_joint_vertex, 'x'),network.get_vertex_attribute(child_joint_vertex, 'y'),network.get_vertex_attribute(child_joint_vertex, 'z'))
    
    #Compare parent frame 0 with coordinates of parent other vertex and parent other joint and store frame 
    if distance_point_point(p_beam_frame_0.Origin,parent_other_vertex_pt) < 200:
        network.set_vertex_attribute(parent_other_vertex, 'connection_frame', p_beam_frame_0_compas)
        network.set_vertex_attribute(parent_joint_vertex, 'connection_frame', p_beam_frame_1_compas)
    if distance_point_point(p_beam_frame_0.Origin,parent_joint_vertex_pt) < 200:
        network.set_vertex_attribute(parent_other_vertex, 'connection_frame', p_beam_frame_1_compas)
        network.set_vertex_attribute(parent_joint_vertex, 'connection_frame', p_beam_frame_0_compas)
    if distance_point_point(ch_beam_frame_0.Origin,child_other_vertex_pt) < 200:
        network.set_vertex_attribute(child_other_vertex, 'connection_frame', ch_beam_frame_0_compas)
        network.set_vertex_attribute(child_joint_vertex, 'connection_frame', ch_beam_frame_1_compas)
    if distance_point_point(ch_beam_frame_0.Origin,child_joint_vertex_pt) < 200:
        network.set_vertex_attribute(child_other_vertex, 'connection_frame', ch_beam_frame_1_compas)
        network.set_vertex_attribute(child_joint_vertex, 'connection_frame', ch_beam_frame_0_compas)
    
    # joint frames
    parent_joint=network.get_vertex_attribute(parent_joint_vertex, 'connection_frame')
    parent_end=network.get_vertex_attribute(parent_other_vertex, 'connection_frame')
    child_joint=network.get_vertex_attribute(child_joint_vertex, 'connection_frame')
    child_end=network.get_vertex_attribute(child_other_vertex, 'connection_frame')
    return parent_end, parent_joint, child_end, child_joint

class ToleranceNetwork(Network):
    #General Network required to 1) generate assembly sequence to 2) perform tolerance analysis
    def __init__(self, joint_edges, beam_edges, ordered_beams, assembly_priority_weights_list, fabrication_requirements_weights_list):
        super(ToleranceNetwork, self).__init__()
        input_dict = {'joint_edges': joint_edges, 'beam_edges': beam_edges, 'ordered_beams': ordered_beams}
        self.attributes.update(input_dict)
        self.build_geometry_network()
        self.build_topology_network (assembly_priority_weights_list)
        self.assembly_sequence_search()
        self.propagate_tolerance_end_to_end()
        self.propagate_tolerance_middle()
        self.display_collisions_stepwise()
        self.adapt_connection()

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

    #GENERATE ASSEMBLY SEQUENCE NETWORK (beams=nodes and connections=edges)
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
        result, beams_parent=kruskal(sorted_directed_edges,nodes,adjacency_dictionary,beams_geometry)
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

    def get_child_and_parent_data(self, beam_nr_assembly_sequence):

        #p_beam, ch_beam, parent_end, parent_joint, child_joint, child_end
        
        #Get TN indexes in sequence
        child_beam_index_TN=int(self.result[beam_nr_assembly_sequence])
        parent_beam_index_TN=self.beams_parent[child_beam_index_TN][0]
        #Get parent and child vertices index in GN
        beam_u_GN, beam_v_GN=get_vertices_index_GN(child_beam_index_TN)
        p_beam_u_GN, p_beam_v_GN=get_vertices_index_GN(parent_beam_index_TN)

        #Get parent and child joint_beam vertices
        parent_other_vertex, parent_joint_vertex, child_other_vertex, child_joint_vertex=get_parent_child_joint_vertices(self, p_beam_u_GN, p_beam_v_GN, beam_u_GN, beam_v_GN)

        p_beam_mesh=get_beam_mesh(self, parent_other_vertex, parent_joint_vertex, 'beam')
        ch_beam_mesh=get_beam_mesh(self, child_other_vertex, child_joint_vertex, 'beam')
        #Get parent and child end frames 
        parent_end, parent_joint, child_end, child_joint=get_parent_child_frames(self, p_beam_mesh, ch_beam_mesh, parent_other_vertex, parent_joint_vertex, child_other_vertex, child_joint_vertex)

        return p_beam_mesh, ch_beam_mesh, parent_end, parent_joint, child_joint, child_end, parent_other_vertex, parent_joint_vertex, child_joint_vertex, child_other_vertex

    def get_deformed_beam_data(self, beam_nr_assembly_sequence):
        #Get TN indexes in sequence
        child_beam_index_TN=int(self.result[beam_nr_assembly_sequence])
        parent_beam_index_TN=self.beams_parent[child_beam_index_TN][0]
        #Get parent and child vertices index in GN
        beam_u_GN, beam_v_GN=get_vertices_index_GN(child_beam_index_TN)
        p_beam_u_GN, p_beam_v_GN=get_vertices_index_GN(parent_beam_index_TN)
        ch_beam=get_beam_mesh(self, beam_u_GN, beam_v_GN, 'deformed_beam')
        p_beam=get_beam_mesh(self, p_beam_u_GN, p_beam_v_GN, 'deformed_beam')
        return p_beam, ch_beam

    def get_middle_frame(self, beam):
        origin_frame=Frame([0, 0, 0], [1, 0, 0], [0, 1, 0])
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

    def propagate_tolerance_middle(self):

        def get_beam_vertices(ch_beam):
            pt_0=ch_beam.beam_vertices[0]
            pt_1=ch_beam.beam_vertices[1]
            pt_2=ch_beam.beam_vertices[2]
            pt_3=ch_beam.beam_vertices[3]
            return pt_0,pt_1,pt_2,pt_3
        #Parameters
        #Tolerance cut
        tolerance_cut_x_value=0
        tolerance_cut_y_value=0

        #Axial tolerance (Worse case x=1.410440759, y=1.813207606)
        axial_tolerance_x_value=1.41
        axial_tolerance_y_value=1.81
        
        transformations=[]
        deformed_beam_display_data=[]

        p_beam, ch_beam, parent_end, parent_joint, child_joint, child_end, parent_other_vertex, parent_joint_vertex, child_joint_vertex, child_other_vertex = self.get_child_and_parent_data(1)

        #Beam 0 - World 0,0,0
        origin_frame=Frame([0, 0, 0], [1, 0, 0], [0, 1, 0])
        #Beam 0 - Middle
        middle_frame=self.get_middle_frame(p_beam)

        F0=Frame(middle_frame.point, middle_frame.xaxis, middle_frame.yaxis)
        T_origin=Transformation.from_frame_to_frame(origin_frame,F0)
        transformations.append(T_origin)
        #Beam 0 - End 0
        F1=Frame(parent_end.point, parent_end.xaxis, parent_end.yaxis)
        F1=F1.transform(Transformation.from_frame(middle_frame).inverse())
        axis_deformation_x=Rotation.from_axis_and_angle(origin_frame.xaxis,math.radians(axial_tolerance_x_value))
        F1.transform(axis_deformation_x)
        F1.transform(Transformation.from_frame(middle_frame))
        T1=Transformation.from_frame_to_frame(middle_frame,F1)
        transformations.append(T1*T_origin)
        #Beam 0 - End 1
        F2=Frame(parent_joint.point, parent_joint.xaxis, parent_joint.yaxis)
        F2=F2.transform(Transformation.from_frame(middle_frame).inverse())
        axis_deformation_x=Rotation.from_axis_and_angle(origin_frame.xaxis,math.radians(-axial_tolerance_x_value))
        F2.transform(axis_deformation_x)
        F2.transform(Transformation.from_frame(middle_frame))
        T2=Transformation.from_frame_to_frame(middle_frame,F2)
        transformations.append(T2*T_origin)

        pt_0, pt_1, pt_2, pt_3=get_beam_vertices(p_beam)

        #Pt 0 - project pt in middle frame
        pt_0_mid=project_point_plane(pt_0,(middle_frame.point,middle_frame.zaxis))
        pt_0_fake=project_point_plane(pt_0_mid,(F2.point, Vector(middle_frame.point, F2.point)))
        int_pt_0=intersection_line_plane(Line(pt_0_mid,pt_0_fake), (F2.point, F2.zaxis))
        
        #Pt 1
        pt_1_mid=project_point_plane(pt_1,(middle_frame.point,middle_frame.zaxis))
        pt_1_fake=project_point_plane(pt_1_mid,(F2.point, Vector(middle_frame.point, F2.point)))
        int_pt_1=intersection_line_plane(Line(pt_1_mid,pt_1_fake), (F2.point, F2.zaxis))

        #Pt 2
        pt_2_mid=project_point_plane(pt_2,(middle_frame.point,middle_frame.zaxis))
        pt_2_fake=project_point_plane(pt_2_mid,(F2.point, Vector(middle_frame.point, F2.point)))
        int_pt_2=intersection_line_plane(Line(pt_2_mid,pt_2_fake), (F2.point, F2.zaxis))

        #Pt 3
        pt_3_mid=project_point_plane(pt_3,(middle_frame.point,middle_frame.zaxis))
        pt_3_fake=project_point_plane(pt_3_mid,(F2.point, Vector(middle_frame.point, F2.point)))
        int_pt_3=intersection_line_plane(Line(pt_3_mid,pt_3_fake), (F2.point, F2.zaxis))

        #Pt 4
        pt_4_mid=project_point_plane(pt_0,(middle_frame.point,middle_frame.zaxis))
        pt_4_fake=project_point_plane(pt_4_mid,(F1.point, Vector(middle_frame.point, F1.point)))
        int_pt_4=intersection_line_plane(Line(pt_4_mid,pt_4_fake), (F1.point, F1.zaxis))

        #Pt 5
        pt_5_mid=project_point_plane(pt_1,(middle_frame.point,middle_frame.zaxis))
        pt_5_fake=project_point_plane(pt_5_mid,(F1.point, Vector(middle_frame.point, F1.point)))
        int_pt_5=intersection_line_plane(Line(pt_5_mid,pt_5_fake), (F1.point, F1.zaxis))

        #Pt 6
        pt_6_mid=project_point_plane(pt_2,(middle_frame.point,middle_frame.zaxis))
        pt_6_fake=project_point_plane(pt_6_mid,(F1.point, Vector(middle_frame.point, F1.point)))
        int_pt_6=intersection_line_plane(Line(pt_6_mid,pt_6_fake), (F1.point, F1.zaxis))

        #Pt 7
        pt_7_mid=project_point_plane(pt_3,(middle_frame.point,middle_frame.zaxis))
        pt_7_fake=project_point_plane(pt_7_mid,(F1.point, Vector(middle_frame.point, F1.point)))
        int_pt_7=intersection_line_plane(Line(pt_7_mid,pt_7_fake), (F1.point, F1.zaxis))

        #Store rail1 (3pts), rail2 (3pts), sweep shape 1 and 2 (two squares = 8pts)
        deformed_beam_display_data.append([[int_pt_2,pt_2_mid,int_pt_6], [int_pt_0,int_pt_1,int_pt_2,int_pt_3,int_pt_0], [int_pt_4,int_pt_5,int_pt_6,int_pt_7,int_pt_4]])
        
        for i in range(1,len(self.result),1):
            p_beam, ch_beam, parent_end, parent_joint, child_joint, child_end, parent_other_vertex, parent_joint_vertex, child_joint_vertex, child_other_vertex = self.get_child_and_parent_data(i)
            #Beam 0 - World 0,0,0
            origin_frame=Frame([0, 0, 0], [1, 0, 0], [0, 1, 0])
            #Beam 0 - Middle
            middle_frame=self.get_middle_frame(ch_beam)
            
            F0=Frame(middle_frame.point, middle_frame.xaxis, middle_frame.yaxis)
            T_origin=Transformation.from_frame_to_frame(origin_frame,F0)
            transformations.append(T_origin)
            #Beam 0 - End 0
            F1=Frame(child_end.point, child_end.xaxis, child_end.yaxis)
            F1=F1.transform(Transformation.from_frame(middle_frame).inverse())
            axis_deformation_x=Rotation.from_axis_and_angle(origin_frame.xaxis,math.radians(axial_tolerance_x_value))
            F1.transform(axis_deformation_x)
            F1.transform(Transformation.from_frame(middle_frame))
            T1=Transformation.from_frame_to_frame(middle_frame,F1)
            transformations.append(T1*T_origin)
            #Beam 0 - End 1
            F2=Frame(child_joint.point, child_joint.xaxis, child_joint.yaxis)
            F2=F2.transform(Transformation.from_frame(middle_frame).inverse())
            axis_deformation_x=Rotation.from_axis_and_angle(origin_frame.xaxis,math.radians(-axial_tolerance_x_value))
            F2.transform(axis_deformation_x)
            F2.transform(Transformation.from_frame(middle_frame))
            T2=Transformation.from_frame_to_frame(middle_frame,F2)
            transformations.append(T2*T_origin)

            pt_0, pt_1, pt_2, pt_3=get_beam_vertices(ch_beam)

            #Pt 0 - project pt in middle frame
            pt_0_mid=project_point_plane(pt_0,(middle_frame.point,middle_frame.zaxis))
            pt_0_fake=project_point_plane(pt_0_mid,(F2.point, Vector(middle_frame.point, F2.point)))
            int_pt_0=intersection_line_plane(Line(pt_0_mid,pt_0_fake), (F2.point, F2.zaxis))
            
            #Pt 1
            pt_1_mid=project_point_plane(pt_1,(middle_frame.point,middle_frame.zaxis))
            pt_1_fake=project_point_plane(pt_1_mid,(F2.point, Vector(middle_frame.point, F2.point)))
            int_pt_1=intersection_line_plane(Line(pt_1_mid,pt_1_fake), (F2.point, F2.zaxis))

            #Pt 2
            pt_2_mid=project_point_plane(pt_2,(middle_frame.point,middle_frame.zaxis))
            pt_2_fake=project_point_plane(pt_2_mid,(F2.point, Vector(middle_frame.point, F2.point)))
            int_pt_2=intersection_line_plane(Line(pt_2_mid,pt_2_fake), (F2.point, F2.zaxis))

            #Pt 3
            pt_3_mid=project_point_plane(pt_3,(middle_frame.point,middle_frame.zaxis))
            pt_3_fake=project_point_plane(pt_3_mid,(F2.point, Vector(middle_frame.point, F2.point)))
            int_pt_3=intersection_line_plane(Line(pt_3_mid,pt_3_fake), (F2.point, F2.zaxis))

            #Pt 4
            pt_4_mid=project_point_plane(pt_0,(middle_frame.point,middle_frame.zaxis))
            pt_4_fake=project_point_plane(pt_4_mid,(F1.point, Vector(middle_frame.point, F1.point)))
            int_pt_4=intersection_line_plane(Line(pt_4_mid,pt_4_fake), (F1.point, F1.zaxis))

            #Pt 5
            pt_5_mid=project_point_plane(pt_1,(middle_frame.point,middle_frame.zaxis))
            pt_5_fake=project_point_plane(pt_5_mid,(F1.point, Vector(middle_frame.point, F1.point)))
            int_pt_5=intersection_line_plane(Line(pt_5_mid,pt_5_fake), (F1.point, F1.zaxis))

            #Pt 6
            pt_6_mid=project_point_plane(pt_2,(middle_frame.point,middle_frame.zaxis))
            pt_6_fake=project_point_plane(pt_6_mid,(F1.point, Vector(middle_frame.point, F1.point)))
            int_pt_6=intersection_line_plane(Line(pt_6_mid,pt_6_fake), (F1.point, F1.zaxis))

            #Pt 7
            pt_7_mid=project_point_plane(pt_3,(middle_frame.point,middle_frame.zaxis))
            pt_7_fake=project_point_plane(pt_7_mid,(F1.point, Vector(middle_frame.point, F1.point)))
            int_pt_7=intersection_line_plane(Line(pt_7_mid,pt_7_fake), (F1.point, F1.zaxis))

            #Store rail1 (3pts), sweep shape 1 and 2 (two squares = 4pts, 4 pts)
            deformed_beam_display_data.append([[int_pt_2,pt_2_mid,int_pt_6], [int_pt_0,int_pt_1,int_pt_2,int_pt_3,int_pt_0], [int_pt_4,int_pt_5,int_pt_6,int_pt_7,int_pt_4]])

        #Store geometry of deformed beam
        display_deformed_beams=[]
        for i in range(len(deformed_beam_display_data)):
            rail_1=rs.AddInterpCurve(deformed_beam_display_data[i][0],3)
            rec_1=rs.AddPolyline(deformed_beam_display_data[i][1])
            rec_2=rs.AddPolyline(deformed_beam_display_data[i][2])
            sweep=rs.AddSweep1(rail_1,[rec_1,rec_2],True)[0]
            rs.CapPlanarHoles(sweep)
            display_deformed_beams.append(sweep)

        #Deformed beam in assembly sequence order
        self.display_deformed_beams=display_deformed_beams

        #Store deformed beams in GN
        for i in range(len(self.result)):
            vert_u, vert_v=get_vertices_index_GN(self.result[i])
            self.set_edge_attribute(vert_u,vert_v,'deformed_beam',display_deformed_beams[i])

    def display_collisions_stepwise(self):
        #Store deformed beams in assembled beams
        display_built_structure=[]
        display_built_structure.append([None])
        counter=0
        for i in range(len(self.result)):
            counter+=1
            beam_meshes_in_step=[]
            for beam_index in range(counter):
                built_beam=self.get_deformed_beam_data(int(beam_index))[1]
                beam_meshes_in_step.append(built_beam)
            display_built_structure.append(beam_meshes_in_step)

        self.display_built_structure=display_built_structure

    def adapt_connection(self):
        #Built structure: display_built_structure
        #Deformed beams in sequence: display_deformed_beams
        #1. Access deformed beam in sequence and get neighbours
        first_beam_in_sequence=self.result[0]
        first_beam_vertices=get_vertices_index_GN(first_beam_in_sequence)



        #2. Check collisions and detect to which neighbour

        #3. Extend or shorten beam







    def propagate_tolerance_end_to_end(self):
        #Parameters

        #Tolerance cut
        tolerance_cut_x_value=0.5
        tolerance_cut_y_value=0

        #Axial tolerance 
        axial_tolerance_x_value=1.4
        axial_tolerance_y_value=0
        
        #2) Get child and parent beams, frames and accumulated tolerances
        p_beam, ch_beam, parent_end, parent_joint, child_joint, child_end, parent_other_vertex, parent_joint_vertex, child_joint_vertex, child_other_vertex = self.get_child_and_parent_data(1)
        
        #Transformations
        transformations=[]

        #Beam 0 - Start postion
        origin_frame=Frame([0, 0, 0], [1, 0, 0], [0, 1, 0])
        T_origin=Transformation.from_frame_to_frame(origin_frame,parent_end)
        transformations.append(T_origin)
        #Beam 0 - Face 0 with cut tolerance
        F0=Frame(parent_end.point, parent_end.xaxis, parent_end.yaxis)
        F0=F0.transform(T_origin.inverse())
        tolerance_cut_x=Rotation.from_axis_and_angle(origin_frame.xaxis,math.radians(tolerance_cut_x_value))
        #tolerance_cut_y=Rotation.from_axis_and_angle(origin_frame.yaxis,math.radians(tolerance_cut_y_value))
        F0.transform(tolerance_cut_x)
        #F0.transform(tolerance_cut_y)
        F0.transform(T_origin)
        T0=Transformation.from_frame_to_frame(parent_end,F0)        
        transformations.append(T0*T_origin)
        #Store cut tolerance in vertex
        self.set_vertex_attribute(parent_other_vertex, 'tolerance', T0*T_origin)#wierd, its and exception
        #Beam 0 - Middle
        middle_frame=self.get_middle_frame(p_beam)
        FM=Frame(middle_frame.point, middle_frame.xaxis, middle_frame.yaxis)
        FM=FM.transform(Transformation.from_frame(parent_end).inverse())
        half_axis_deformation_x=Rotation.from_axis_and_angle(origin_frame.xaxis,math.radians(axial_tolerance_x_value/3))
        #half_axis_deformation_y=Rotation.from_axis_and_angle(origin_frame.yaxis,math.radians(axial_tolerance_y_value/3))
        FM.transform(half_axis_deformation_x)
        #FM.transform(half_axis_deformation_y)
        FM.transform(Transformation.from_frame(parent_end))
        TM=Transformation.from_frame_to_frame(parent_end,FM)
        transformations.append(T0*TM*T_origin)
        #Beam 0 - Face 1 with axis deviation
        F1=Frame(parent_joint.point, parent_joint.xaxis, parent_joint.yaxis)
        F1=F1.transform(Transformation.from_frame(middle_frame).inverse())
        axis_deformation_x=Rotation.from_axis_and_angle(origin_frame.xaxis,math.radians(axial_tolerance_x_value))
        F1.transform(axis_deformation_x)
        axis_deformation_y=Rotation.from_axis_and_angle(origin_frame.yaxis,math.radians(axial_tolerance_y_value))
        F1.transform(axis_deformation_y)
        F1.transform(Transformation.from_frame(middle_frame))
        T1=Transformation.from_frame_to_frame(F0,F1)
        transformations.append(T0*T1*T_origin)
        #Beam 0 - Face 1 with cut tolerance
        F2=Frame(F1.point, F1.xaxis, F1.yaxis)
        F2=F2.transform(Transformation.from_frame(F1).inverse())
        F2.transform(tolerance_cut_x)
        #F2.transform(tolerance_cut_y)
        F2.transform(Transformation.from_frame(F1))
        T2=Transformation.from_frame_to_frame(F1,F2)
        transformations.append(T0*T2*T1*T_origin)
        #Store cut tolerance in vertex
        self.set_vertex_attribute(parent_joint_vertex, 'tolerance', T0*T2*T1*T_origin)
        
        #Propagate Tolerances
        for i in range(1,len(self.result),1):
            p_beam, ch_beam, parent_end, parent_joint, child_joint, child_end, parent_other_vertex, parent_joint_vertex, child_joint_vertex, child_other_vertex = self.get_child_and_parent_data(i)  

            #Transformation to parent joint
            T_origin_4=Transformation.from_frame_to_frame(origin_frame,parent_joint) 
            #Get tolerance of parent joint
            acc_tolerance_1=self.get_vertex_attribute(parent_joint_vertex, 'tolerance')
            #Frame to accumulated tolerance
            FI_4=Frame.from_transformation(acc_tolerance_1)#replace with tolerance TI*T0_3*T_origin_3
            #Transformation from parent joint to parent cut tolerance
            TI_4=Transformation.from_frame_to_frame(parent_joint, FI_4)
            transformations.append(TI_4*T_origin_4)
            TI_5=Transformation.from_frame_to_frame(parent_joint, child_joint)
            transformations.append(TI_4*TI_5*T_origin_4)

            #Transformation with cut tolerance
            F0_4=Frame(parent_joint.point, parent_joint.xaxis, parent_joint.yaxis)

            F0_4=F0_4.transform(T_origin_4.inverse())
            tolerance_cut_x=Rotation.from_axis_and_angle(origin_frame.xaxis,math.radians(tolerance_cut_x_value))
            #tolerance_cut_y=Rotation.from_axis_and_angle(origin_frame.yaxis,math.radians(tolerance_cut_y_value))
            F0_4.transform(tolerance_cut_x)
            #F0_4.transform(tolerance_cut_y)
            F0_4.transform(T_origin_4)
            T0_4=Transformation.from_frame_to_frame(parent_joint,F0_4)
            transformations.append(TI_4*TI_5*T0_4*T_origin_4)
            #Store cut tolerance in vertex (just in case)
            self.set_vertex_attribute(child_joint_vertex, 'tolerance', TI_4*TI_5*T0_4*T_origin_4)
            
            #Transformation to middle
            middle_frame_4=self.get_middle_frame(ch_beam)
            FM_4=Frame(middle_frame_4.point, middle_frame_4.xaxis, middle_frame_4.yaxis)
            FM_4=FM_4.transform(Transformation.from_frame(child_joint).inverse())
            FM_4.transform(half_axis_deformation_x)
            #FM_4.transform(half_axis_deformation_y)
            FM_4.transform(Transformation.from_frame(child_joint))
            TM_4=Transformation.from_frame_to_frame(child_joint,FM_4)
            transformations.append(TI_4*TM_4*TI_5*T0_4*T_origin_4)

            #Transformation to axis deviation
            F1_4=Frame(child_end.point, child_end.xaxis, child_end.yaxis)
            F1_4=F1_4.transform(Transformation.from_frame(middle_frame_4).inverse())
            F1_4.transform(axis_deformation_x)
            #F1_4.transform(axis_deformation_y)
            F1_4.transform(Transformation.from_frame(middle_frame_4))
            self.F1_4=F1_4
            T1_4=Transformation.from_frame_to_frame(child_joint,F1_4)
            transformations.append(TI_4*T1_4*TI_5*T0_4*T_origin_4)

            #Transformation with cut tolerance
            F2_4=Frame(F1_4.point, F1_4.xaxis, F1_4.yaxis)
            F2_4=F2_4.transform(Transformation.from_frame(F1_4).inverse())
            F2_4.transform(tolerance_cut_x)
            #F2_4.transform(tolerance_cut_y)
            F2_4.transform(Transformation.from_frame(F1_4))
            T2_4=Transformation.from_frame_to_frame(F1_4,F2_4)
            transformations.append(TI_4*T2_4*T1_4*TI_5*T0_4*T_origin_4)#TI y T2 pueden ser invertidos
            #Store cut tolerance in vertex
            self.set_vertex_attribute(child_other_vertex, 'tolerance', TI_4*T2_4*T1_4*TI_5*T0_4*T_origin_4)

        #Display deformations
        
        #Beam 1 - exception
        displayed_deformations=[]
        pt_0_frame=Frame.from_transformation(transformations[0])
        pt_1_frame=Frame.from_transformation(transformations[2])
        line_0=Line((pt_0_frame.point[0],pt_0_frame.point[1],pt_0_frame.point[2]),(pt_1_frame.point[0],pt_1_frame.point[1],pt_1_frame.point[2]))
        displayed_deformations.append(line_0)
        pt_0_frame=Frame.from_transformation(transformations[2])
        pt_1_frame=Frame.from_transformation(transformations[3])
        line_0=Line((pt_0_frame.point[0],pt_0_frame.point[1],pt_0_frame.point[2]),(pt_1_frame.point[0],pt_1_frame.point[1],pt_1_frame.point[2]))
        displayed_deformations.append(line_0)
        
        #Rest of beams
        for i in range(7,len(transformations),6):
            pt_0_frame=Frame.from_transformation(transformations[i])
            pt_1_frame=Frame.from_transformation(transformations[i+1])
            line_0=Line((pt_0_frame.point[0],pt_0_frame.point[1],pt_0_frame.point[2]),(pt_1_frame.point[0],pt_1_frame.point[1],pt_1_frame.point[2]))
            displayed_deformations.append(line_0)
            pt_0_frame=Frame.from_transformation(transformations[i+1])
            pt_1_frame=Frame.from_transformation(transformations[i+2])
            line_0=Line((pt_0_frame.point[0],pt_0_frame.point[1],pt_0_frame.point[2]),(pt_1_frame.point[0],pt_1_frame.point[1],pt_1_frame.point[2]))
            displayed_deformations.append(line_0)

        self.transformations=transformations
        self.displayed_deformations=displayed_deformations    
        
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
