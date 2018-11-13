from compas.datastructures.network import Network
from compas_fab.fab.geometry import Frame, Transformation, Translation, Rotation
from compas.geometry.elements import Line, Point
from compas.geometry import distance_point_point
from compas.geometry import project_point_plane
from compas.geometry import intersection_line_plane
from compas_fab.fab.grasshopper.utilities.drawing import xdraw_frame
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

def check_connectivity(current_beam, adjacency, beams_geometry, result, count):
    #Type of beam (0 = bottom beams, 1 = middle beams, 2 = upper beams) 
    beams_type={0:1, 1:1, 2:0, 3:2, 4:1, 5:1, 6:0, 7:2, 8:1, 9:1, 10:0, 11:2, 12:1, 13:1, 14:0, 15:2, 16:1, 
    17:1, 18:0, 19:2, 20:1, 21:1, 22:0, 23:2, 24:1, 25:0, 26:2, 27:1, 28:0 ,29:2, 30:1, 31:0, 32:2, 33:1,
    34:1, 35:0, 36:2, 37:1, 38:1, 39:0 ,40:2 ,41:1, 42:1, 43:1, 44:0, 45:2, 46:1, 47:1, 48:0, 49:2, 50:1,
    51:1, 52:0, 53:2, 54:1, 55:1, 56:1, 57:0, 58:2, 59:1, 60:1, 61:0, 62:2, 63:1, 64:1, 65:0, 66:2, 67:1,
    68:1, 69:1, 70:0, 71:2}

    #List to store values for the second iteration, restore every second iteration
    if count==None or count==0:
        global temporary_result
        temporary_result=[]
    
    print "current_beam:", current_beam

    check=False
    nbrs=set(adjacency[current_beam])

    #if beam is 0 and it is the first one, just place it (this could be better)
    if beams_type[current_beam]==0 and count==None:
        temporary_result.append(str(current_beam))
        check=True

    elif beams_type[current_beam]==0:
        for nbr_node in set(nbrs):
            nbr_node_type=beams_type[nbr_node]
            if nbr_node_type==0 and str(nbr_node) in result:
                temporary_result.append(str(current_beam))
                check=True

    elif beams_type[current_beam]==1:
        for nbr_node in set(nbrs):
            nbr_node_type=beams_type[nbr_node]
            if nbr_node_type==0:
                if str(nbr_node) in result or str(nbr_node) in temporary_result:
                    check=True

    #If beam is a top beam
    elif beams_type[current_beam]==2:
        print "type 2, current_beam", current_beam
        counter=0
        middle_nbrs=0
        #Iterate nbrs
        for nbr_node in set(nbrs):
            #Get nbr type
            nbr_node_type=beams_type[nbr_node]
            #If nbr is middle beam
            print "nbrs and type", nbr_node, nbr_node_type
            if nbr_node_type==1:
                #Count how many nbrs are middle beams
                middle_nbrs+=1
                #Count built nbr middle beams
                if str(nbr_node) in result:
                    counter+=1
        if counter==middle_nbrs:
            print "counter", counter, "middle_nbrs counter", middle_nbrs
            check=True
    
    return check

    """
    if beam is 0 and it is the first one, just place it
    if beam is 0 and it is not the first one, check if any nbr was placed
    if beam is 1 check if its nbr 0 was placed
    if beam is 2 check if 2 nbrs 2 were placed
    """

# Method to perform Kruskal's Algorithm    
def kruskal(data,nodes,adjacency_dictionary,beams_geometry):

    distance = 0
    result = list()
    nodes = init(nodes)
    forward_counters={}
    beams_propagation_path={}
    stored_goal=[]
    predecessors=[]

    escape_count = 0

    while len(data):
        counter_1=0
        counter_2=1
        escape_count += 1
        if escape_count > 100000:
            raise Exception('Probably in an infinity loop, Aborting')
        if escape_count==1:
            counter_1=None
        weighted_edge = data.pop(0)
        if find(nodes, weighted_edge[0]) != find(nodes, weighted_edge[1]):
            if not check_connectivity (int(weighted_edge[0]), adjacency_dictionary, beams_geometry, result, counter_1) or not check_connectivity (int(weighted_edge[1]), adjacency_dictionary, beams_geometry, result, counter_2):
                key = '%s-%s' % (weighted_edge[0], weighted_edge[1])
                if key in forward_counters:
                    forward_counters[key]+=1
                else:
                    forward_counters[key]=1
                forward_count=forward_counters[key]
                data.insert(forward_count, weighted_edge)
                continue
            forward_counters = {}
            union(nodes, weighted_edge[0], weighted_edge[1])
            beam_1=weighted_edge[0]
            beam_2=weighted_edge[1]
            print "weights 1 and 2",weighted_edge[0], weighted_edge[1] 
            print "=============================================================================>add beams 1 and 2:",beam_1,beam_2
            result.append(beam_1)
            result.append(beam_2)
            print "result", result
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
    

class ToleranceNetwork(Network):
    #General Network required to 1) generate assembly sequence to 2) perform tolerance analysis
    def __init__(self, joint_edges, beam_edges, ordered_beams, weights_list):
        super(ToleranceNetwork, self).__init__() 
        input_dict = {'joint_edges': joint_edges, 'beam_edges': beam_edges, 'ordered_beams': ordered_beams}
        self.attributes.update(input_dict)
        self.build_geometry_network()
        self.build_topology_network (weights_list)
        self.assembly_sequence_search()

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
        print result
        self.beams_parent=beams_parent

        # It may be needed!!!
        """
        #Correct first values (To be fixed)
        building_sequence.insert(0,[building_sequence[0][0]])
        building_sequence.insert(2,[building_sequence[2][0], building_sequence[2][1], building_sequence[2][2]])
        building_sequence.pop(3)
        self.building_sequence=building_sequence 
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
