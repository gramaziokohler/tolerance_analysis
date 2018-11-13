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
r.seed(1)

__author__     = 'Augusto Gandia'
__copyright__  = 'Copyright 2018, Gramazio Kohler Research - ETH Zurich'
__license__    = 'MIT'
__email__      = 'gandia@arch.ethz.ch'

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

# Method to perform Kruskal's Algorithm    
def kruskal(data,cities):
    distance = 0
    result = list()
    cities = init(cities)
    for edge in range(len(data)):
        path = data.pop(0)
        #If the two cities in the path do not have the same
        #canonical representative, join them together, then 
        #add path to result and calculate distance
        if find(cities,path[0]) != find(cities,path[1]):
            union(cities, path[0],path[1])
            #result.extend((path[0] + ' -> ' + path[1], '(' + str(path[2]) + ' miles)'))
            result.extend((path[0], path[1]))
            distance += path[2]
    return result#,distance

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
    """ Multiple networks for tolerance analysis of spatial structures """
    def __init__(self, edges_joint, edges_beam, ordered_beams, weights_list):
        super(ToleranceNetwork, self).__init__() 
        input_dict = {'edges_joint': edges_joint, 'edges_beam': edges_beam, 'ordered_beams': ordered_beams}
        self.attributes.update(input_dict)
        self.generate_vertices()
        self.generate_joint_edges()
        self.store_connectivity_in_member_edges()
        self.generate_topology_network()
        self.MST_Kruskal(weights_list)
        #self.draw_MST_Kruskal()

    def draw_MST_Kruskal(self):
        expanded_vertices_temp_list=self.sorted_data[:]
        for i in expanded_vertices_temp_list:
            if [i[1],i[0],i[2]] in expanded_vertices_temp_list:
                expanded_vertices_temp_list.remove([i[1],i[0],i[2]])
        #setup
        directed_graph=Digraph()
        #format
        directed_graph.attr(size='8,5', ranksep='5')
        #add edges
        for edge in expanded_vertices_temp_list:
            directed_graph.attr('node', shape='circle')
            directed_graph.edge("B "+str(edge[0]),"B "+str(edge[1]), label= "W "+str(edge[2]))
        #render
        directed_graph.render(filename = 'C:/Users/gandiaa/Documents/projects/tolerance_analysis/connectivity_graph', cleanup=True)       
    
    def generate_vertices(self):
        #Add in network, vertices of edge beams
        for edge_beam in range(len(self.attributes ['edges_beam'])):
            #Add edge vertex u
            position = self.attributes ['edges_beam'][edge_beam][0]
            u=self.add_vertex(attr_dict={'x': position[0], 'y' : position[1], 'z' : position[2], 'vertex_type': 'member'})
            #Add edge vertex v
            position = self.attributes ['edges_beam'][edge_beam][1]
            v=self.add_vertex(attr_dict={'x': position[0], 'y' : position[1], 'z' : position[2], 'vertex_type': 'member'})
            #Add attribute edge type and asociate beam
            neighbours_member_edges=[]
            self.add_edge(u,v, {'edge_type': 'member','beam': self.attributes ['ordered_beams'][edge_beam], 'u_coordinate':self.vertex_coordinates(u), 'v_coordinate': self.vertex_coordinates(v), 'neighbours_member_edges': neighbours_member_edges})

    def generate_joint_edges(self):
        store_beam_u=[]
        store_beam_v=[]
        for edge_joint in range (len(self.attributes['edges_joint'])):
            joint_u=self.attributes ['edges_joint'][edge_joint][0]
            joint_v=self.attributes ['edges_joint'][edge_joint][1]
            for u,v,attr in self.edges(data=True):
                beam_u=attr['u_coordinate']
                beam_v=attr['v_coordinate']
                if distance_point_point(joint_u,beam_u) < 100:
                    joint_new_vertex_u=[]
                    joint_new_vertex_u.append(u)
                if distance_point_point(joint_u,beam_v) < 100:
                    joint_new_vertex_u=[]
                    joint_new_vertex_u.append(v)
                if distance_point_point(joint_v,beam_u) < 100:
                    joint_new_vertex_v=[]
                    joint_new_vertex_v.append(u)
                if distance_point_point(joint_v,beam_v) < 100:
                    joint_new_vertex_v=[]
                    joint_new_vertex_v.append(v)
            store_beam_u.append(joint_new_vertex_u[0])
            store_beam_v.append(joint_new_vertex_v[0])
        for iterate in range(len(store_beam_v)):
            self.add_edge(store_beam_u[iterate], store_beam_v[iterate], {'edge_type': 'joint','beam': None})

    def store_connectivity_in_member_edges(self):
        #store connectivity in joint edges
        for u,v,attr in self.edges(data=True):#181
            if attr['edge_type']=='joint':
                connected_joint_edges_list=edge_connected_edges(self,u,v) #per beam edge a list of connected joint edges
                prev_list=[]
                #filter connected joint edges and store connected member edges
                for joint_edge in connected_joint_edges_list:
                    if self.get_edge_attribute(joint_edge[0],joint_edge[1],'edge_type')=='member':   
                        prev_list.append((joint_edge[0],joint_edge[1])) 
                #get existing neighbours from first edge
                first_edge_neighbours=self.get_edge_attribute(prev_list[0][0],prev_list[0][1],'neighbours_member_edges')
                first_edge_neighbours.append(prev_list[1])
                #get existing neighbours from second edge
                sec_edge_neighbours=self.get_edge_attribute(prev_list[1][0],prev_list[1][1],'neighbours_member_edges')
                sec_edge_neighbours.append(prev_list[0])
    
    def generate_topology_network(self):
        #This "topology network" is an inversion of the "geometry_network" by turning beams into vertices
        self.topology_network=TopologyNetwork(self)

    def MST_Kruskal(self, weights_list):
        self.adjacency_dict=self.topology_network.adjacency_dictionary
        unsorted_data=[]
        expanded_vertices=[]
        #iter topology_network vertices
        for key, key_connected_vertices in self.adjacency_dict.items():
            #key=current vertex key, value=key of vertices connected to current vertex
            for connected_vertex in key_connected_vertices:
                #format for kruskal e.g [[1,61], [1,53], [1,63]]
                expanded_vertices.append(str(key))
                expanded_vertices.append(str(connected_vertex))
                unsorted_data.append([str(key),str(connected_vertex), weights_list[key] + weights_list[connected_vertex]]) #weights_list[key] + weights_list[connected_vertex] 
        self.sorted_data, sorted_vertices_keys=sorted(unsorted_data, key=operator.itemgetter(2)), sorted(set(expanded_vertices))
        #Run kruskal
        self.mst_result_list=kruskal(self.sorted_data[:], sorted_vertices_keys)

class TopologyNetwork(Network):
    def __init__(self, geometry_network):
        super(TopologyNetwork, self).__init__() 
        input_dict = {'edges': geometry_network.edges(data=True)}
        self.attributes.update(input_dict)
        self.build_inverted_network()
        #self.build_tolerance_analysis_network()

    def build_inverted_network(self):
        #To translate from member being an edge to member being a vertex 
        #only the u value of each member is used and divided by 2.
        #Thus it turns from being (u=0,u=2,u=4...) to (u=0,u=1,u=2...) 
        #iter member edges of geometry network
        for u,v,attr in self.attributes['edges']:
            if attr['edge_type']=='member':
                #get midpoint for each member edge of geometry network
                beam_edge_mid=midpoint_line((attr['u_coordinate'],attr['v_coordinate']))
                #create new vertex and use as coordinate the midpoint of u and v
                self.add_vertex(attr_dict={'x': beam_edge_mid[0], 'y' : beam_edge_mid[1], 'z' : beam_edge_mid[2]})#add beam_vertex
        
        #Create adjacency dictionary
        adjacency_dict={}
        for u,v,attr in self.attributes['edges']:
            if attr['edge_type']=='member':
                temp_connected_vertex=[]
                #iter connected member edges of geometry network
                for connected_vertices in attr['neighbours_member_edges']:
                    #store connected member as its u value divided by 2 
                    temp_connected_vertex.append(connected_vertices[0]/2)
                adjacency_dict[u/2]=temp_connected_vertex
        self.adjacency_dictionary=adjacency_dict

        for u, attr in self.vertices(data=True):
            self.set_vertex_attribute(u, 'connected_vertices', self.adjacency_dictionary[u])

    def build_tolerance_analysis_network(self):
        for u,v,attr in self.attributes['edges']:
            if attr['edge_type']=='member':
                print None#u,v,attr

if __name__ == "__main__":
    temp_frames_array = [] 
