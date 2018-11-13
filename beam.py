import spatial_timber_assemblies.geometry_generation.helper_functions as hp
import compas.geometry.spatial as spatial
import Rhino.Geometry as rg
import scriptcontext

__author__ = 'Arash Adel'
__email__ = '<adel@arch.ethz.ch>'
__copyright__ = 'Copyright 2017, Gramazio Kohler Research - ETH Zurich'


"""
**********************************************************************************
In this module, Beam Class and its Methods for the generation of the structural
elements (horizontal, verticals and diagonal beams) are defined.
**********************************************************************************
"""


class Beam(object):

    def __init__(self, beam_attr_dict):
        '''
        TODO: change all lists to tuples for better performance
        The Beam class is initialized with an attribute dictionary.
        attr_dict = {"init_end_pts": initial_end_pts, "end_planes": end_planes,
        "dim": beam_dim = [thickness, height],
        "xAxis":beam_x_axis,  "yAxis": beam_y_axis}
        The Beam class is initialized with following inputs:
        end_planes: list of two planes to define the short cuts of the beam.
        dim: dimensions of the beam profile in y and z direction of the frame.

        It has methods for generating the geometry of the beam.
        It should keep track of the neighboring elements.
        It should have the fabrication data associated with it
        # direction of the deepest thickness (Rhino.Geometry.Vector3d)
        self.orinetation   = Rhino.Geometry.Vector3d(_orinetation)
        self.orientation: orientation of the beam (frame.zAxis without the z.val)
        z value of self.orientation (orientation.Z) should be 0 for verticals/diagonals/chords or -1 for rafters
        # Profile thickness in direction of z
        self.height = _height
        # Profile thickness in direction of y
        self.width  = _width
        Type of beam (0 = bottom chord, 1 = top chord, 2 = verticals and diagonals, 3 = wall rafter, 4= slab rafter)
        '''
        # setting beam attributes
        self._set_beam_attributes(beam_attr_dict)
        # weight of the beam in KG
        self.weight = 0
        # center of the mass for the beam
        self.center_mass = None
        # list of neighboring beams
        self.neigbors = []  # TODO: include this information
        # list of the beam necessary fabrication data
        self.fab_data = []
        # Suggested Gripping Plane(s)
        self.gripping_planes = []
        # TODO: include the following attribute for the beam
        self.governing_neighbours = None
        # each module has an interior center point to be used for defining
        # beam in/ex vertices and other necessary info
        # information after measuring the fabricated beam and define its tolerance
        self.fabricated_tolerance = None
        # structural bar instance key that gets filled after structural analysis
        self.structure_bar_key = None
        # Loads for structural analysis
        self.loads = []
        # Screw Information
        # self.screws = (screws_bot, screws_top)
        # screws_bot = ((screw_0_point, screw_0_vec), (screw_1_point, screw_1_vec),...)
        self.screws = []
        self.is_saw_blade_shifted = None  # If shifted, the vector of the shift is passed!
        # TODO: Add milling info for the facade on the bottom and top cord
        self.facade_milling_info = None
        self.steel_plate_milling_info = None
        self.high_tension_connection_milling_info = None
        self.high_tension_connection_screws = None  # Two points (anchor point and end point)
        self.high_tension_connection_screws_vertical_beam = None
        # High Tension beam attribute
        self.is_high_tension_beam = (False, None)
        self.has_high_tension_screws = {
            "bot": False, "top": False}
        self.is_sharing_axis_point_with_other = (False, None)

        # If a high-tension beam, set the attribute to True
        # Note: need to run this after all the beams of the modules are generated
        # from the building class

    @classmethod
    def from_side_edge(cls, beam_side_edge, offset_dir, beam_attr_dict):
        """
        Initialize a beam instance from its edge as input (not axis).
        """

        # Calculate the beam axis points.
        z_axis = rg.Vector3d(beam_attr_dict.get("zAxis"))
        z_axis.Unitize()
        axis_vec = beam_side_edge.UnitTangent
        if rg.Vector3d.Multiply(offset_dir, z_axis) < 0:
            z_axis.Reverse()
            x_axis = rg.Vector3d.CrossProduct(axis_vec, z_axis)
            x_axis.Reverse()
        else:
            x_axis = rg.Vector3d.CrossProduct(axis_vec, z_axis)

        beam_dim = beam_attr_dict.get("dim")
        beam_thickness = beam_dim[0]
        half_thickness = beam_thickness / 2.0
        beam_height = beam_dim[1]
        half_height = beam_height / 2.0
        translation_vec_x = rg.Vector3d.Multiply(x_axis, half_thickness)
        translation_vec_z = rg.Vector3d.Multiply(z_axis, half_height)
        translation_vec = rg.Vector3d.Add(translation_vec_x, translation_vec_z)
        # Find beam init axis sp (using the profile info)
        beam_axis_sp = rg.Point3d.Add(beam_side_edge.From, translation_vec)

        # Find beam init axis ep (use the edge info and add it to the beam init sp)
        beam_axis_ep = rg.Point3d.Add(beam_side_edge.To, translation_vec)

        init_axis_pts = [beam_axis_sp, beam_axis_ep]
        beam_attr_dict["init_end_pts"] = init_axis_pts
        beam_attr_dict["ref_side_edge"] = beam_side_edge
        beam = cls(beam_attr_dict)
        return beam

    def _set_beam_attributes (self, beam_attr_dict):
        """
        finds and sets the attributes for the beam.
        """
        self.tolerance = scriptcontext.doc.ModelAbsoluteTolerance
        self.attr_dict = {"init_end_pts": None, "end_planes": None,
                          "dim": None, "zAxis": None, "type": None,
                          "parent_bar": None, "parent_building": None,
                          "is_corner_vertical": False, "is_corner_diagonal": False,
                          "corner_diagonal_aligned_edge": None,
                          "is_opening_beam": False,
                          "parent_floor": None,
                          "parent_walls": [], "parent_slabs": [],
                          "is_window_main_beam": False,
                          "is_window_cross_beam": False,
                          "parent_module": None,
                          "ref_side_edge": None, "mesh":None, "beam_vertices": None}

        self.attr_dict.update(beam_attr_dict)
        self.ref_side_edge = self.attr_dict["ref_side_edge"]  # if initialized from side edge
        self.is_window_main_beam = self.attr_dict.get("is_window_main_beam")
        self.is_window_cross_beam = self.attr_dict.get("is_window_cross_beam")
        self.initial_end_pts = self.attr_dict.get("init_end_pts")
        self.beam_vertices = self.attr_dict.get("beam_vertices")
        # TODO: make zAxis consistent for all beam and change it to beam.orientation
        # TODO: get rid of zAxis
        self.zAxis = rg.Vector3d(self.attr_dict.get("zAxis"))
        self.zAxis.Unitize()
        self.type = self.attr_dict.get("type")
        if self.type == 0 or self.type == 1:
            self.zAxis.Z = 0.0
        self.parent_bar = self.attr_dict.get("parent_bar")
        self.parent_building = self.attr_dict.get("parent_building")
        self.parent_floor = self.attr_dict.get("parent_floor")
        self.parent_walls = self.attr_dict.get("parent_walls")
        self.parent_slabs = self.attr_dict.get("parent_slabs")
        self.end_planes = self.attr_dict.get("end_planes")
        self.dim = self.attr_dict.get("dim")
        self.thickness = self.dim[0]
        self.half_thickness = self.thickness / 2.0
        self.height = self.dim[1]
        self.half_height = self.height / 2.0
        self.is_corner_diagonal = self.attr_dict.get("is_corner_diagonal")
        self.corner_diagonal_aligned_edge = self.attr_dict.get("corner_diagonal_aligned_edge")
        self.is_corner_vertical = self.attr_dict.get("is_corner_vertical")
        self.parent_module = self.attr_dict.get("parent_module")

        # Generate the axis unit vector
        self.axis_vec = self.gen_axis_unit_vec(self.initial_end_pts)
        # List of the start and end point of bar axis
        self.axis_end_points = self.gen_axis_end_points(self.end_planes)
        # Regenerating the end planes
        self.end_planes = self.re_gen_end_planes()
        # Generating the beam frame
        self.frame = self.gen_frame(self.axis_end_points)
        # Generating beam vertices
        beam_vertices_info = self.gen_beam_vertices(self.frame, self.axis_vec, self.end_planes)
        self.vertices = beam_vertices_info[0]
        self.vertices_tuple = beam_vertices_info[1]
        # Generating beam faces and side planes
        beam_faces_info = self.gen_beam_faces(self.vertices)
        self.faces = beam_faces_info[0]
        self.side_planes = beam_faces_info[1]
        self.side_frames = beam_faces_info[2]
        self.mesh=self.attr_dict.get("mesh")
        # Generating the beam geometry

        # beam_vol_info = self.gen_beam_vol(self.faces, self.vertices, self.tolerance)
        # self.polysurface = beam_vol_info[0]
        # self.mesh = beam_vol_info[1]

        # Replace zAxis with self.orientation
        self.orientation = self.re_gen_beam_orientation(self.vertices)
        # tuple of four long side edges of the beam
        self.side_edges = self.gen_beam_side_edges(self.vertices)

    def reset_attributes(self, new_beam_attr_dict):
        """
        Reset the attribute of the beam.
        new_beam_attr_dict = {"init_end_pts": initial_end_pts, "end_planes": end_planes,
                  "dim": [80.0,120.0], "zAxis": z_axis}
        "init_end_pts": List of start and end point of the beam axis
        "end_planes": List of the start and end cut planes of the beam
        "dim": beam_dim = [thickness, height]
        "zAxis": rg vector
        """
        self.attr_dict.update(new_beam_attr_dict)
        self.initial_end_pts = self.attr_dict.get("init_end_pts")
        self.zAxis = rg.Vector3d(self.attr_dict.get("zAxis"))
        self.zAxis.Unitize()
        if self.type == 0 or self.type == 1:
            self.zAxis.Z = 0.0
        self.end_planes = self.attr_dict.get("end_planes")
        self.dim = self.attr_dict.get("dim")
        self.thickness = self.dim[0]
        self.half_thickness = self.thickness / 2.0
        self.height = self.dim[1]
        self.half_height = self.height / 2.0

        # Generate the axis unit vector
        self.axis_vec = self.gen_axis_unit_vec(self.initial_end_pts)
        # List of the start and end point of bar axis
        self.axis_end_points = self.gen_axis_end_points(self.end_planes)
        # Regenerating the end planes
        self.end_planes = self.re_gen_end_planes()
        # Generating the beam frame
        self.frame = self.gen_frame(self.axis_end_points)
        # Generating beam vertices
        beam_vertices_info = self.gen_beam_vertices(self.frame, self.axis_vec, self.end_planes)
        self.vertices = beam_vertices_info[0]
        self.vertices_tuple = beam_vertices_info[1]
        # Generating beam faces and side planes
        beam_faces_info = self.gen_beam_faces(self.vertices)
        self.faces = beam_faces_info[0]
        self.side_planes = beam_faces_info[1]
        self.side_frames = beam_faces_info[2]
        # Generating the beam geometry
        beam_vol_info = self.gen_beam_vol(self.faces, self.vertices, self.tolerance)
        self.polysurface = beam_vol_info[0]
        self.mesh = beam_vol_info[1]
        self.orientation = self.re_gen_beam_orientation(self.vertices)
        # tuple of four long side edges of the beam
        self.side_edges = self.gen_beam_side_edges(self.vertices)

    def get_attribute(self, beam_attr):
        """
        Return a specific beam attribute.
        TODO: double check that this function is properly written.
        """
        try:
            return self.__dict__[beam_attr]
        except KeyError:
            print "beam does not have the input attribute!"
            # return None

    def get_corner_vertical_neighbor_diagonals(self):
        """
        Check if the beam is a corner diagonal and return its attached diagonals.
        """
        pass

    # -----------------------------------------------------------------------
    # Methods to update beam attributes
    # -----------------------------------------------------------------------

    def set_structure_bar_key(self, new_structure_bar_key):
        """
        Sets a new structure bar key for the beam.
        """
        self.structure_bar_key = new_structure_bar_key

    # -----------------------------------------------------------------------
    # Methods to generate beam geometry data
    # -----------------------------------------------------------------------

    def gen_axis_unit_vec(self, initial_end_pts):
        """
        Generates the unit axis vector of the beam.
        """
        return hp.create_line_unit_vec(initial_end_pts[0], initial_end_pts[1])

    def gen_axis_end_points(self, end_planes):
        """
        Generate the list of start and end point of bar axis.
        This is used for structural calculations.
        change to rg point3d
        TODO: calculate initi_mid_pt with rg
        """
        init_mid_pt_xyz = spatial.midpoint_line(self.initial_end_pts[0], self.initial_end_pts[1])
        init_mid_pt = rg.Point3d(init_mid_pt_xyz[0], init_mid_pt_xyz[1], init_mid_pt_xyz[2])
        infin_axis_line = hp.infinite_line(init_mid_pt, self.axis_vec)
        axis_st_pt = hp.intersect_line_plane(infin_axis_line, end_planes[0])
        axis_en_pt = hp.intersect_line_plane(infin_axis_line, end_planes[1])
        return (axis_st_pt, axis_en_pt)

    def re_gen_end_planes(self):
        """
        Regenerates the beam cut_planes at the axis end points.
        """
        end_plane_0 = rg.Plane(self.axis_end_points[0], self.end_planes[0].XAxis, self.end_planes[0].YAxis)
        end_plane_1 = rg.Plane(self.axis_end_points[1], self.end_planes[1].XAxis, self.end_planes[1].YAxis)
        return (end_plane_0, end_plane_1)

    def gen_frame(self, axis_end_points):
        """
        Generates and sets the frame for the beam on the middle of axis line.
        TODO: maybe better to have frame_zAxis and xaxis as inputs (double check)
        """
        axis_mid_point = rg.Point3d((axis_end_points[0] + axis_end_points[1]) / 2.0)
        frame_zAxis = self.zAxis
        xaxis = self.axis_vec
        yaxis = rg.Vector3d.CrossProduct(frame_zAxis, xaxis)
        return rg.Plane(axis_mid_point, xaxis, yaxis)

    def gen_rect_corners(self, beam_frame):
        """
        Returns corners of a rectangle on the frame plane of the beam
        rectangle width = beam thickness
        rectangle length = beam height
        Output: list of four corners
                pt_3----------pt_0
                    |        |
                    |        |
                    |   cp   |
                    |        |
                    |        |
                pt_2----------pt_1
        """
        cen_pt = beam_frame.Origin
        translation_vec_y = rg.Vector3d.Multiply(beam_frame.YAxis, self.half_thickness)
        translation_vec_z = rg.Vector3d.Multiply(beam_frame.ZAxis, self.half_height)
        translation_vec_1 = rg.Vector3d.Add(translation_vec_y, translation_vec_z)
        translation_vec_2 = rg.Vector3d.Add(translation_vec_y, rg.Vector3d.Negate(translation_vec_z))
        translation_vec_3 = rg.Vector3d.Add(rg.Vector3d.Negate(translation_vec_y), rg.Vector3d.Negate(translation_vec_z))
        translation_vec_4 = rg.Vector3d.Add(rg.Vector3d.Negate(translation_vec_y), translation_vec_z)
        corner_0 = rg.Point3d.Add(cen_pt, translation_vec_1)
        corner_1 = rg.Point3d.Add(cen_pt, translation_vec_2)
        corner_2 = rg.Point3d.Add(cen_pt, translation_vec_3)
        corner_3 = rg.Point3d.Add(cen_pt, translation_vec_4)
        corners = [corner_0, corner_1, corner_2, corner_3]
        return corners

    def gen_beam_vertices(self, beam_frame, beam_axis_vec, beam_end_planes):
        """
        Returns points of the structural element volume
        """
        vertices_bot = []
        vertices_bot_tuple = []
        vertices_top_tuple = []
        vertices_top = []
        profile_corners = self.gen_rect_corners(beam_frame)
        for corner in profile_corners:
            infin_line = hp.infinite_line(corner, beam_axis_vec)
            sp_ep_line = hp.intersect_line_planes(infin_line, beam_end_planes)
            vertex_bot = sp_ep_line.From
            vertex_top = sp_ep_line.To
            vertices_bot.append(vertex_bot)
            vertices_top.append(vertex_top)
            vertices_bot_tuple.append((vertex_bot.X, vertex_bot.Y, vertex_bot.Z))
            vertices_top_tuple.append((vertex_top.X, vertex_top.Y, vertex_top.Z))
        vertices_bot = tuple(vertices_bot)
        vertices_top = tuple(vertices_top)
        vertices_bot_tuple = tuple(vertices_bot_tuple)
        vertices_top_tuple = tuple(vertices_top_tuple)
        return (vertices_bot, vertices_top), (vertices_bot_tuple, vertices_top_tuple)

    def gen_beam_faces(self, beam_vertices):
        """
        Generates the faces of the beam out of two sets of 4 points (8 vertices)
        Inputs: 2 lists of points (4 each) for the bottom and top face
        pts_bot: list of four corner points for the bottom face
        pts_top: list of four points for the top face
        self.faces = a list of the six breps of the beam volume
        """
        faces = []
        side_frames = []  # list of six frames (one on each beam face) facing outwards
        # vertices_bot = beam_vertices[0:4]
        vertices_bot = beam_vertices[0]
        # vertices_top = beam_vertices[4:]
        vertices_top = beam_vertices[1]
        prof_bot_pts = [vertices_bot[0], vertices_bot[1], vertices_bot[2], vertices_bot[3]]
        bot_frame = rg.Plane(vertices_bot[0], vertices_bot[3], vertices_bot[1])
        prof_top_pts = [vertices_top[0], vertices_top[1], vertices_top[2], vertices_top[3]]
        top_frame = rg.Plane(vertices_top[0], vertices_top[1], vertices_top[3])
        prof_sd_01_pts = [vertices_bot[0], vertices_top[0], vertices_top[1], vertices_bot[1]]
        plane_sd_01 = rg.Plane(vertices_bot[0], vertices_bot[1], vertices_top[0])
        prof_sd_02_pts = [vertices_bot[1], vertices_top[1], vertices_top[2], vertices_bot[2]]
        plane_sd_02 = rg.Plane(vertices_bot[1], vertices_bot[2], vertices_top[1])
        prof_sd_03_pts = [vertices_bot[2], vertices_top[2], vertices_top[3], vertices_bot[3]]
        plane_sd_03 = rg.Plane(vertices_bot[2], vertices_bot[3], vertices_top[2])
        prof_sd_04_pts = [vertices_bot[3], vertices_top[3], vertices_top[0], vertices_bot[0]]
        plane_sd_04 = rg.Plane(vertices_bot[3], vertices_bot[0], vertices_top[3])
        profiles_pts = [prof_bot_pts, prof_top_pts, prof_sd_01_pts, prof_sd_02_pts, prof_sd_03_pts, prof_sd_04_pts]
        side_frames = [bot_frame, top_frame, plane_sd_01, plane_sd_02, plane_sd_03, plane_sd_04]
        # drawing faces and add them to the list of faces
        for profile_pts in profiles_pts:
            beam_face = rg.Brep.CreateFromCornerPoints(
                profile_pts[0], profile_pts[1], profile_pts[2], profile_pts[3], 0)
            faces.append(beam_face)

        faces = tuple(faces)
        return faces, (plane_sd_01, plane_sd_02, plane_sd_03, plane_sd_04), side_frames

    def gen_beam_side_edges(self, beam_vertices):
        """
        Generates the four side long edges of the beam geometry out of two sets of 4 points (8 vertices)
        Inputs: 2 lists of points (4 each) for the bottom and top face
        pts_bot: list of four corner points for the bottom face
        pts_top: list of four points for the top face
        """
        side_edges = []

        vertices_bot = beam_vertices[0]
        vertices_top = beam_vertices[1]
        for bot_index, bot_vert in enumerate(vertices_bot):
            top_vert = vertices_top[bot_index]
            edge_line = rg.Line(bot_vert, top_vert)
            side_edges.append(edge_line)
        side_edges = tuple(side_edges)
        return side_edges

    def re_gen_beam_orientation(self, beam_vertices):
        """
        Regenerates the orientation unit vector of the beam.
        orientation_vec.z = 0.0
        """
        bot_vertices = beam_vertices[0]
        line_0 = rg.Line(bot_vertices[0], bot_vertices[3])
        line_1 = rg.Line(bot_vertices[1], bot_vertices[2])
        sp = line_0.PointAt(0.50)
        ep = line_1.PointAt(0.50)
        orientation_vec = rg.Vector3d(ep - sp)
        orientation_vec.Unitize()
        return orientation_vec

    # -----------------------------------------------------------------------
    # Methods to add screws information to the beam
    # -----------------------------------------------------------------------
    def check_is_beam_high_tension(self):
        """
        Checks if the beam is a high tension beam and
        add necessary information.
        NOTE: this method is called in the building class after
        all beams are generated.
        """
        is_high_tension_bar = self.parent_building.get_bar_attribute(
            self.parent_bar, "is_high_tension_bar")
        if is_high_tension_bar[0] == False:
            self.is_high_tension_beam = (False, None)
        else:
            bot_top_neigh_bar_dict = is_high_tension_bar[1]
            bot_neighbor_bar = bot_top_neigh_bar_dict["bot_neighbor"]
            top_neighbor_bar = bot_top_neigh_bar_dict["top_neighbor"]
            # print "beam bar: ", self.parent_bar
            # print bot_neighbor_bar, top_neighbor_bar
            if bot_neighbor_bar is not None:
                bot_neighbor_beam = self.parent_building._find_bar_beam_in_module(
                    bot_neighbor_bar, self.parent_module, 2)
            else:
                bot_neighbor_beam = None
            if top_neighbor_bar is not None:
                top_neighbor_beam = self.parent_building._find_bar_beam_in_module(
                    top_neighbor_bar, self.parent_module, 2)
            else:
                top_neighbor_beam = None
            bot_top_neigh_dict = {
                "bot_neighbor": bot_neighbor_beam,
                "top_neighbor": top_neighbor_beam}
            # Add has_high_tension_screws attr to neighbor beams
            if bot_neighbor_beam is not None:
                bot_neighbor_beam.has_high_tension_screws["bot"] = True
            if top_neighbor_beam is not None:
                top_neighbor_beam.has_high_tension_screws["top"] = True
            self.is_high_tension_beam = (True, bot_top_neigh_dict)
            # Add has_high_tension_screws attr to beam
            self.has_high_tension_screws = {
                "bot": True, "top": True}

    def add_screws_information(self, screws_information):
        """
        Adds the screws information to the beam class.
        Screws information are generated after the FEM analysis is performed, in
        the analysis package.
        # self.screws = (screws_bot, screws_top)
        # screws_bot = ((screw_0_point, screw_0_vec), (screw_1_point, screw_1_vec),...)
        # screws_top = ((screw_0_point, screw_0_vec), (screw_1_point, screw_1_vec),...)
        """
        # TODO: define bottom and top screws
        self.screws = screws_information

    def add_screw_to_beam_screws(self, new_screw_information, screw_side="bottom"):
        """
        Adds the screws information to the beam class. This function used
        for the screws at the either end of the beam.
        Screws information are generated after the FEM analysis is performed, in
        the analysis package.
        # self.screws = (screws_bot, screws_top)
        # screws_bot = ((screw_0_point, screw_0_vec), (screw_1_point, screw_1_vec),...)
        # screws_top = ((screw_0_point, screw_0_vec), (screw_1_point, screw_1_vec),...)
        """
        # TODO: define bottom and top screws
        beam_screws = self.screws[:]
        if beam_screws == []:
            beam_screws = [[], []]
        if screw_side == "bottom":
            beam_screws[0].append(new_screw_information)
        elif screw_side == "top":
            beam_screws[1].append(new_screw_information)
        else:
            raise Exception("Side is not defined correctly!")

        self.screws = beam_screws

    def add_screw_to_horizontal_beam_screws(self, new_screw_information):
        """
        Adds the screws information to the beam class, this function is not used for
        the screws that are at the either end of the beam.
        Screws information are generated after the FEM analysis is performed, in
        the analysis package.
        # self.screws = (screws_bot, screws_top)
        # screws[0] = screws_bot = ((screw_0_point, screw_0_vec), (screw_1_point, screw_1_vec),...)
        # screws[1] = screws_top = ((screw_0_point, screw_0_vec), (screw_1_point, screw_1_vec),...)
        # screws[2] = all the screws that belong to the cross bar and are a result of the main bars.
        """
        beam_screws = self.screws[:]
        if beam_screws == []:
            beam_screws = [[], [], []]
        elif len(beam_screws) == 2:
            beam_screws.append([])
        beam_screws[2].append(new_screw_information)
        self.screws = beam_screws

    # -----------------------------------------------------------------------
    # Methods to work with fabrication tolerances and sensors data
    # -----------------------------------------------------------------------

    def get_outside_vertices(self):
        """
        Returns four vertices of the beam that face outside of the parent module.
        output:
        a list of four vertices [bot_left, bot_right, top_left, top_right]

        TODO: for interior beams there needs to be a logic based on
              maybe where the structure is exposed!
        """
        raise("Not implemented!")

    def get_inside_vertices(self):
        """
        Returns four vertices of the beam that face inside of the parent module.
        output:
        a list of four vertices [bot_left, bot_right, top_left, top_right]

        TODO: for interior beams there needs to be a logic based on
              maybe where the structure is exposed!
        """
        raise("Not implemented!")

    def is_fabricated(self):
        """
        Returns True if beam is fabricated (check the self.fabricated_tolerance).
        """
        if self.fabricated_tolerance is None:
            return False
        else:
            return True
