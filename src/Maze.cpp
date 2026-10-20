/************************************************************************
     File:        Maze.cpp

     Author:     
                  Stephen Chenney, schenney@cs.wisc.edu
     Modifier
                  Yu-Chi Lai, yu-chi@cs.wisc.edu

     Comment:    
						(c) 2001-2002 Stephen Chenney, University of Wisconsin at Madison

						Class header file for Maze class. Manages the maze.
		

     Platform:    Visio Studio.Net 2003 (converted to 2005)

*************************************************************************/

#include "Maze.h"
#include "LineSeg.h"
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <time.h>
#include <vector>
#include <FL/Fl.h>
#include <FL/fl_draw.h>
#include <FL/gl.h>

//###################################################################
// Portal-visibility math (Project 2).
// World: maze lies in the XY plane, z is up. Floor z = -1,
// ceiling z = +1, viewer z = 0.
// View space: x_v = forward, y_v = left.
// Screen (OpenGL 2D, origin at center): x right, y up,
// screen_x = -focal * y_v / x_v, screen_y = focal * z / x_v.
//
// EXTRA (windows, for bonus points):
// A window edge is opaque (blocks walking) but has a see-through
// horizontal slit in world-Z: [WINDOW_SILL, WINDOW_TOP].
// It is drawn as two solid quads (below sill, above top) plus a portal
// opening. Everything behind is screen-space clipped to the opening quad,
// so no pixel (apart from floor/ceiling background) is drawn twice.
// Only glColor3f / glBegin(GL_POLYGON) / glVertex2f / glEnd are used.
//###################################################################
namespace Vis {

struct Frustum {
    float vx, vy;   // viewer location
    float lx, ly;   // unit vector along left boundary
    float rx, ry;   // unit vector along right boundary
};

// Window slit in world Z. Must stay strictly inside (-1, 1).
const float WINDOW_SILL = -0.35f;
const float WINDOW_TOP  =  0.45f;

inline float Cross2(float ax, float ay, float bx, float by) {
    return ax * by - ay * bx;
}

// Clip segment (x1,y1)->(x2,y2) against one half-plane of the frustum.
// isLeft==true  -> keep points to the RIGHT of left boundary
//                 (cross(L, P-V) <= eps).
// isLeft==false -> keep points to the LEFT of right boundary
//                 (cross(R, P-V) >= -eps).
// Returns false if the whole segment is outside.
inline bool ClipToHalfPlane(const Frustum &F, bool isLeft,
                            float &x1, float &y1, float &x2, float &y2) {
    const float EPS = 1.0e-6f;
    float dx = isLeft ? F.lx : F.rx;
    float dy = isLeft ? F.ly : F.ry;

    float c1 = Cross2(dx, dy, x1 - F.vx, y1 - F.vy);
    float c2 = Cross2(dx, dy, x2 - F.vx, y2 - F.vy);

    bool in1 = isLeft ? (c1 <= EPS) : (c1 >= -EPS);
    bool in2 = isLeft ? (c2 <= EPS) : (c2 >= -EPS);

    if (in1 && in2)
        return true;
    if (!in1 && !in2)
        return false;

    // One point in, one out: intersect segment with infinite line V + t*D.
    float ex = x2 - x1;
    float ey = y2 - y1;
    float det = Cross2(dx, dy, ex, ey); // cross(D, e)
    if (fabs(det) < 1.0e-12)
        return false; // parallel (should not happen for straddling case)

    // s = cross(D, V - A) / cross(D, e)
    float s = Cross2(dx, dy, F.vx - x1, F.vy - y1) / det;
    if (s < 0.0f) s = 0.0f;
    if (s > 1.0f) s = 1.0f;
    float ix = x1 + s * ex;
    float iy = y1 + s * ey;

    if (!in1) {
        x1 = ix; y1 = iy;
    } else {
        x2 = ix; y2 = iy;
    }
    return true;
}

inline bool ClipEdgeToFrustum(const Frustum &F,
                              float &x1, float &y1,
                              float &x2, float &y2) {
    if (!ClipToHalfPlane(F, true, x1, y1, x2, y2))
        return false;
    if (!ClipToHalfPlane(F, false, x1, y1, x2, y2))
        return false;
    float dx = x2 - x1, dy = y2 - y1;
    if (dx * dx + dy * dy < 1.0e-12f)
        return false;
    return true;
}

// Restrict frustum F to the (already clipped) portal segment.
// The new boundaries are the rays from V through the two endpoints.
inline Frustum RestrictFrustum(const Frustum &F,
                               float x1, float y1,
                               float x2, float y2) {
    float ax = x1 - F.vx, ay = y1 - F.vy;
    float bx = x2 - F.vx, by = y2 - F.vy;
    float alen = (float)sqrt(ax * ax + ay * ay);
    float blen = (float)sqrt(bx * bx + by * by);
    Frustum NF = F;
    if (alen < 1.0e-6f || blen < 1.0e-6f) {
        // Portal endpoint essentially at the viewer: no valid restriction.
        NF.lx = NF.rx; NF.ly = NF.ry;
        return NF;
    }
    ax /= alen; ay /= alen;
    bx /= blen; by /= blen;
    // cross(A,B) > 0 means B is CCW (more left) from A.
    if (Cross2(ax, ay, bx, by) > 0.0f) {
        NF.lx = bx; NF.ly = by;
        NF.rx = ax; NF.ry = ay;
    } else {
        NF.lx = ax; NF.ly = ay;
        NF.rx = bx; NF.ry = by;
    }
    return NF;
}

inline bool FrustumValid(const Frustum &F) {
    // Left must be strictly CCW from right (positive, < 180 deg).
    return Cross2(F.rx, F.ry, F.lx, F.ly) > 1.0e-6f;
}

// Screen-space wall quad, ordered left -> right on screen.
struct WallQuad {
    float sxL, sybL, sytL; // left  (bottom, top)
    float sxR, sybR, sytR; // right (bottom, top)
};

// Project a clipped world-space edge to screen.
// Returns false for degenerate (zero-width) walls.
inline bool ProjectWall(float x1, float y1, float x2, float y2,
                        float vx, float vy, float cosD, float sinD,
                        float focal, WallQuad &q) {
    float dx1 = x1 - vx, dy1 = y1 - vy;
    float dx2 = x2 - vx, dy2 = y2 - vy;
    float xf1 = dx1 * cosD + dy1 * sinD;   // forward
    float yl1 = -dx1 * sinD + dy1 * cosD;  // left
    float xf2 = dx2 * cosD + dy2 * sinD;
    float yl2 = -dx2 * sinD + dy2 * cosD;

    // Frustum clipping guarantees xf > 0; guard against degeneracy.
    if (xf1 < 1.0e-6f) xf1 = 1.0e-6f;
    if (xf2 < 1.0e-6f) xf2 = 1.0e-6f;

    float sx1 = -focal * yl1 / xf1;
    float sx2 = -focal * yl2 / xf2;
    float yb1 = -focal / xf1, yt1 = focal / xf1;
    float yb2 = -focal / xf2, yt2 = focal / xf2;

    // Order left->right on screen to avoid bow-tie quads.
    if (sx1 <= sx2) {
        q.sxL = sx1; q.sybL = yb1; q.sytL = yt1;
        q.sxR = sx2; q.sybR = yb2; q.sytR = yt2;
    } else {
        q.sxL = sx2; q.sybL = yb2; q.sytL = yt2;
        q.sxR = sx1; q.sybR = yb1; q.sytR = yt1;
    }
    if (fabs(q.sxR - q.sxL) < 1.0e-6)
        return false;
    return true;
}

// Window projection: full wall plus sill/top heights, left->right.
struct WindowProj {
    float sxL, sxR;
    float ybL, ybR;   // z = -1
    float ysL, ysR;   // z = SILL
    float ytL, ytR;   // z = TOP
    float ycL, ycR;   // z = +1
};

inline bool ProjectWindow(float x1, float y1, float x2, float y2,
                          float vx, float vy, float cosD, float sinD,
                          float focal, WindowProj &w) {
    float dx1 = x1 - vx, dy1 = y1 - vy;
    float dx2 = x2 - vx, dy2 = y2 - vy;
    float xf1 = dx1 * cosD + dy1 * sinD;
    float yl1 = -dx1 * sinD + dy1 * cosD;
    float xf2 = dx2 * cosD + dy2 * sinD;
    float yl2 = -dx2 * sinD + dy2 * cosD;
    if (xf1 < 1.0e-6f) xf1 = 1.0e-6f;
    if (xf2 < 1.0e-6f) xf2 = 1.0e-6f;
    float sx1 = -focal * yl1 / xf1;
    float sx2 = -focal * yl2 / xf2;
    float yb1 = -focal / xf1, ys1 = focal * WINDOW_SILL / xf1;
    float yt1 = focal * WINDOW_TOP / xf1, yc1 = focal / xf1;
    float yb2 = -focal / xf2, ys2 = focal * WINDOW_SILL / xf2;
    float yt2 = focal * WINDOW_TOP / xf2, yc2 = focal / xf2;
    if (sx1 <= sx2) {
        w.sxL = sx1; w.ybL = yb1; w.ysL = ys1; w.ytL = yt1; w.ycL = yc1;
        w.sxR = sx2; w.ybR = yb2; w.ysR = ys2; w.ytR = yt2; w.ycR = yc2;
    } else {
        w.sxL = sx2; w.ybL = yb2; w.ysL = ys2; w.ytL = yt2; w.ycL = yc2;
        w.sxR = sx1; w.ybR = yb1; w.ysR = ys1; w.ytR = yt1; w.ycR = yc1;
    }
    if (fabs(w.sxR - w.sxL) < 1.0e-6)
        return false;
    return true;
}

// ---- Screen-space convex-polygon clipping (Sutherland-Hodgman) ----
// All polygons here are convex and CCW: BL -> BR -> TR -> TL.
struct Vec2 { float x, y; };
typedef std::vector<Vec2> Poly;

inline Vec2 IntersectLines(Vec2 p1, Vec2 p2, Vec2 a, Vec2 b) {
    float d1x = p2.x - p1.x, d1y = p2.y - p1.y;
    float d2x = b.x - a.x, d2y = b.y - a.y;
    float det = d1x * d2y - d1y * d2x; // cross(d1, d2)
    Vec2 out = p1;
    if (fabs(det) < 1.0e-12)
        return out;
    // t = cross(a - p1, d2) / cross(d1, d2)
    float t = ((a.x - p1.x) * d2y - (a.y - p1.y) * d2x) / det;
    out.x = p1.x + t * d1x;
    out.y = p1.y + t * d1y;
    return out;
}

inline Poly ClipPolyAgainstEdge(const Poly &subj, Vec2 a, Vec2 b) {
    Poly out;
    if (subj.empty())
        return out;
    const float EPS = 1.0e-6f;
    for (size_t i = 0; i < subj.size(); i++) {
        Vec2 cur = subj[i];
        Vec2 prev = subj[(i + subj.size() - 1) % subj.size()];
        float cCur = (b.x - a.x) * (cur.y - a.y) - (b.y - a.y) * (cur.x - a.x);
        float cPrev = (b.x - a.x) * (prev.y - a.y) - (b.y - a.y) * (prev.x - a.x);
        bool inCur = (cCur >= -EPS);
        bool inPrev = (cPrev >= -EPS);
        if (inCur) {
            if (!inPrev)
                out.push_back(IntersectLines(prev, cur, a, b));
            out.push_back(cur);
        } else if (inPrev) {
            out.push_back(IntersectLines(prev, cur, a, b));
        }
    }
    return out;
}

inline Poly IntersectConvex(const Poly &subj, const Poly &clip) {
    if (subj.empty() || clip.empty())
        return Poly();
    Poly out = subj;
    for (size_t j = 0; j < clip.size(); j++) {
        Vec2 a = clip[j];
        Vec2 b = clip[(j + 1) % clip.size()];
        out = ClipPolyAgainstEdge(out, a, b);
        if (out.empty())
            break;
    }
    return out;
}

inline Poly QuadPoly(float sxL, float yL0, float sxR, float yR0,
                     float sxR2, float yR1, float sxL2, float yL1) {
    Poly p;
    Vec2 v;
    v.x = sxL; v.y = yL0; p.push_back(v);
    v.x = sxR; v.y = yR0; p.push_back(v);
    v.x = sxR2; v.y = yR1; p.push_back(v);
    v.x = sxL2; v.y = yL1; p.push_back(v);
    return p;
}

struct ScreenClip {
    bool active;
    Poly poly;
    ScreenClip() : active(false) {}
    ScreenClip(bool a, const Poly &p) : active(a), poly(p) {}
};

// Draw a screen-space polygon with 2D calls only.
inline void DrawPoly(const float *color, const Poly &p) {
    if (p.size() < 3)
        return;
    glColor3f(color[0], color[1], color[2]);
    glBegin(GL_POLYGON);
    for (size_t i = 0; i < p.size(); i++)
        glVertex2f(p[i].x, p[i].y);
    glEnd();
}

} // namespace Vis

// Window test: opaque edge painted with sentinel glass color (0,1,1).
// Random BuildMaze colors live in [0.25, 0.75], so this never fires
// accidentally. Users/TA can make any wall a window by editing the maze
// file color to "0 1 1", or by pressing G in front of a wall.
bool Maze::Is_Window_Edge(const Edge *e) const {
    if (!e || !e->opaque)
        return false;
    return (e->color[0] < 0.05f && e->color[1] > 0.95f && e->color[2] > 0.95f);
}

// Project a clipped world-space edge to screen and draw the wall quad.
// Floor is at z=-1, ceiling at z=+1, viewer at z=0.
// Honors the incoming screen-space clip (for views through windows).
inline void DrawWall(Edge *e,
                     float x1, float y1, float x2, float y2,
                     float vx, float vy, float cosD, float sinD,
                     float focal, const Vis::ScreenClip &clip) {
    Vis::WallQuad q;
    if (!Vis::ProjectWall(x1, y1, x2, y2, vx, vy, cosD, sinD, focal, q))
        return;
    Vis::Poly wall = Vis::QuadPoly(q.sxL, q.sybL, q.sxR, q.sybR,
                                   q.sxR, q.sytR, q.sxL, q.sytL);
    Vis::Poly todraw = clip.active ? Vis::IntersectConvex(wall, clip.poly) : wall;
    float c[3] = { e->color[0], e->color[1], e->color[2] };
    Vis::DrawPoly(c, todraw);
}

void DrawCellRecursive(Cell *cell, const Vis::Frustum &F,
                       float cosD, float sinD, float focal,
                       unsigned int frame, const Vis::ScreenClip &clip,
                       std::vector<Cell*> &path);

void DrawCellRecursive(Cell *cell, const Vis::Frustum &F,
                       float cosD, float sinD, float focal,
                       unsigned int frame, const Vis::ScreenClip &clip) {
    std::vector<Cell*> path;
    DrawCellRecursive(cell, F, cosD, sinD, focal, frame, clip, path);
}

void DrawCellRecursive(Cell *cell, const Vis::Frustum &F,
                       float cosD, float sinD, float focal,
                       unsigned int frame) {
    Vis::ScreenClip noClip;
    std::vector<Cell*> path;
    DrawCellRecursive(cell, F, cosD, sinD, focal, frame, noClip, path);
}

static bool InPath(const std::vector<Cell*> &path, Cell *c) {
    for (size_t k = 0; k < path.size(); k++)
        if (path[k] == c) return true;
    return false;
}

void DrawCellRecursive(Cell *cell, const Vis::Frustum &F,
                       float cosD, float sinD, float focal,
                       unsigned int frame, const Vis::ScreenClip &clip,
                       std::vector<Cell*> &path) {
    if (!cell)
        return;
    // Path-based cycle guard (not global frame counter).
    // Windows add portal loops to the transparent spanning tree, so the same
    // cell can be legitimately reached via two disjoint frusta (directly
    // through the window vs. the long way around). A global visited flag
    // lets whichever branch runs first win and culls the other, which
    // flickers as the frustum changes with forward/backward motion.
    // Branches from one cell have disjoint angular intervals, so redrawing
    // via another path does not overdraw: keep only anti-cycle on the stack.
    if (InPath(path, cell))
        return;
    path.push_back(cell);

    for (int i = 0; i < 4; i++) {
        Edge *e = cell->edges[i];
        if (!e)
            continue;
        float x1 = e->endpoints[Edge::START]->posn[Vertex::X];
        float y1 = e->endpoints[Edge::START]->posn[Vertex::Y];
        float x2 = e->endpoints[Edge::END]->posn[Vertex::X];
        float y2 = e->endpoints[Edge::END]->posn[Vertex::Y];

        float cx1 = x1, cy1 = y1, cx2 = x2, cy2 = y2;
        if (!Vis::ClipEdgeToFrustum(F, cx1, cy1, cx2, cy2))
            continue; // not visible in this frustum

        // Window: opaque glass wall with a horizontal slit opening.
        // opaque==true so collision still blocks walking; rendering draws
        // lower/upper solids and recurses through the opening as a portal.
        bool isWindow = (e->opaque &&
                         e->color[0] < 0.05f && e->color[1] > 0.95f &&
                         e->color[2] > 0.95f);
        if (isWindow) {
            // Exact-visibility: only the front face owns this edge.
            char side = e->Point_Side(F.vx, F.vy);
            if (side != Edge::ON && e->neighbors[side] != cell)
                continue;
            Vis::WindowProj w;
            if (!Vis::ProjectWindow(cx1, cy1, cx2, cy2,
                                    F.vx, F.vy, cosD, sinD, focal, w))
                continue;
            // Partition of the full wall quad: bottom solid, opening, top.
            Vis::Poly bot = Vis::QuadPoly(w.sxL, w.ybL, w.sxR, w.ybR,
                                           w.sxR, w.ysR, w.sxL, w.ysL);
            Vis::Poly top = Vis::QuadPoly(w.sxL, w.ytL, w.sxR, w.ytR,
                                           w.sxR, w.ycR, w.sxL, w.ycL);
            Vis::Poly open = Vis::QuadPoly(w.sxL, w.ysL, w.sxR, w.ysR,
                                            w.sxR, w.ytR, w.sxL, w.ytL);
            // Frame tint for solids so the window reads as a frame,
            // still disjoint from the opening (no overdraw).
            float frameC[3] = { 0.10f, 0.45f, 0.55f };
            Vis::Poly botC = clip.active ?
                Vis::IntersectConvex(bot, clip.poly) : bot;
            Vis::Poly topC = clip.active ?
                Vis::IntersectConvex(top, clip.poly) : top;
            Vis::DrawPoly(frameC, botC);
            Vis::DrawPoly(frameC, topC);

            Vis::Poly newPoly = clip.active ?
                Vis::IntersectConvex(open, clip.poly) : open;
            if (newPoly.size() < 3)
                continue;
            Vis::Frustum NF = Vis::RestrictFrustum(F, cx1, cy1, cx2, cy2);
            if (!Vis::FrustumValid(NF))
                continue;
            Cell *n = e->Neighbor(cell);
            if (!n) {
                // Exterior window: show outside (sky above horizon,
                // ground below). The two quads partition the opening,
                // then are clipped to the incoming clip: no overdraw.
                Vis::Poly outBot = Vis::QuadPoly(w.sxL, w.ysL, w.sxR, w.ysR,
                                                  w.sxR, 0.0f, w.sxL, 0.0f);
                Vis::Poly outTop = Vis::QuadPoly(w.sxL, 0.0f, w.sxR, 0.0f,
                                                  w.sxR, w.ytR, w.sxL, w.ytL);
                Vis::Poly ob = clip.active ?
                    Vis::IntersectConvex(outBot, clip.poly) : outBot;
                Vis::Poly ot = clip.active ?
                    Vis::IntersectConvex(outTop, clip.poly) : outTop;
                float ground[3] = { 0.25f, 0.50f, 0.25f };
                float sky[3] = { 0.55f, 0.78f, 1.00f };
                Vis::DrawPoly(ground, ob);
                Vis::DrawPoly(sky, ot);
                continue;
            }
            if (InPath(path, n))
                continue;
            Vis::ScreenClip nclip(true, newPoly);
            DrawCellRecursive(n, NF, cosD, sinD, focal, frame, nclip, path);
        } else if (e->opaque) {
            // Draw each opaque edge exactly once: only from the cell
            // on the viewer's side of the edge (its front face).
            // The other neighbor must skip it. This keeps exact
            // visibility regardless of visit order: the viewing cell
            // always holds the complete visible piece.
            char side = e->Point_Side(F.vx, F.vy);
            if (side != Edge::ON && e->neighbors[side] != cell)
                continue;
            DrawWall(e, cx1, cy1, cx2, cy2, F.vx, F.vy, cosD, sinD, focal, clip);
        } else {
            Cell *n = e->Neighbor(cell);
            if (!n)
                continue;
            if (InPath(path, n))
                continue;
            Vis::Frustum NF = Vis::RestrictFrustum(F, cx1, cy1, cx2, cy2);
            if (!Vis::FrustumValid(NF))
                continue;
            DrawCellRecursive(n, NF, cosD, sinD, focal, frame, clip, path);
        }
    }
    path.pop_back();
}

const char Maze::X = 0;
const char Maze::Y = 1;
const char Maze::Z = 2;

const float Maze::BUFFER = 0.1f;


//**********************************************************************
//
// * Constructor for the maze exception
//======================================================================
MazeException::
MazeException(const char *m)
//======================================================================
{
	message = new char[strlen(m) + 4];
	strcpy(message, m);
}


//**********************************************************************
//
// * Constructor to create the default maze
//======================================================================
Maze::
Maze(const int nx, const int ny, const float sx, const float sy)
//======================================================================
{
	// Build the connectivity structure.
	Build_Connectivity(nx, ny, sx, sy);

	// Make edges transparent to create a maze.
	Build_Maze();

	// Set the extents of the maze
	Set_Extents();

	// Default values for the viewer.
	viewer_posn[X] = viewer_posn[Y] = viewer_posn[Z] = 0.0;
	viewer_dir = 0.0;
	viewer_fov = 45.0;

	// Always start on the 0th frame.
	frame_num = 0;
}


//**********************************************************************
//
// * Construtor to read in precreated maze
//======================================================================
Maze::
Maze(const char *filename)
//======================================================================
{
	char    err_string[128];
	FILE    *f;
	int	    i;

	// Open the file
	if ( ! ( f = fopen(filename, "r") ) )
		throw new MazeException("Maze: Couldn't open file");

	// Get the total number of vertices
	if ( fscanf(f, "%d", &num_vertices) != 1 )
		throw new MazeException("Maze: Couldn't read number of vertices");

	// Read in each vertices
	vertices = new Vertex*[num_vertices];
	for ( i = 0 ; i < num_vertices ; i++ ) {
		float x, y;
		if ( fscanf(f, "%g %g", &x, &y) != 2 )	{
			sprintf(err_string, "Maze: Couldn't read vertex number %d", i);
			throw new MazeException(err_string);
		}
		vertices[i] = new Vertex(i, x, y);
	}

	// Get the number of edges
	if ( fscanf(f, "%d", &num_edges) != 1 )
		throw new MazeException("Maze: Couldn't read number of edges");

	// read in all edges
	edges = new Edge*[num_edges];
	for ( i = 0 ; i < num_edges ; i++ ){
		int     vs, ve, cl, cr, o;
		float	r, g, b;
		if ( fscanf(f, "%d %d %d %d %d %g %g %g",
						&vs, &ve, &cl, &cr, &o, &r, &g, &b) != 8) {
			sprintf(err_string, "Maze: Couldn't read edge number %d", i);
			throw new MazeException(err_string);
		}
		edges[i] = new Edge(i, vertices[vs], vertices[ve], r, g, b);
		edges[i]->Add_Cell((Cell*)cl, Edge::LEFT);
		edges[i]->Add_Cell((Cell*)cr, Edge::RIGHT);
		edges[i]->opaque = o ? true : false;
	}

	// Read in the number of cells
	if ( fscanf(f, "%d", &num_cells) != 1 )
		throw new MazeException("Maze: Couldn't read number of cells");


	// Read in all cells
	cells = new Cell*[num_cells];
	for ( i = 0 ; i < num_cells ; i++ )	{
		int epx, epy, emx, emy;
		if ( fscanf(f, "%d %d %d %d", &epx, &epy, &emx, &emy) != 4 ){
			sprintf(err_string, "Maze: Couldn't read cell number %d", i);
			throw new MazeException(err_string);
		}
		cells[i] = new Cell(i, epx >= 0 ? edges[epx] : NULL,
									epy >= 0 ? edges[epy] : NULL,
									emx >= 0 ? edges[emx] : NULL,
									emy >= 0 ? edges[emy] : NULL);
		if ( cells[i]->edges[0] ) {
			if ( cells[i]->edges[0]->neighbors[0] == (Cell*)i )
				cells[i]->edges[0]->neighbors[0] = cells[i];
			else if ( cells[i]->edges[0]->neighbors[1] == (Cell*)i )
				cells[i]->edges[0]->neighbors[1] = cells[i];
			else	{
				sprintf(err_string,
						  "Maze: Cell %d not one of edge %d's neighbors",
							i, cells[i]->edges[0]->index);
				throw new MazeException(err_string);
			}
		}

		if ( cells[i]->edges[1] )	{
			if ( cells[i]->edges[1]->neighbors[0] == (Cell*)i )
				cells[i]->edges[1]->neighbors[0] = cells[i];
			else if ( cells[i]->edges[1]->neighbors[1] == (Cell*)i )
				cells[i]->edges[1]->neighbors[1] = cells[i];
			else {
				sprintf(err_string,
							"Maze: Cell %d not one of edge %d's neighbors",
							i, cells[i]->edges[1]->index);
				throw new MazeException(err_string);
			}
		}
		if ( cells[i]->edges[2] ) {
			if ( cells[i]->edges[2]->neighbors[0] == (Cell*)i )
				cells[i]->edges[2]->neighbors[0] = cells[i];
			else if ( cells[i]->edges[2]->neighbors[1] == (Cell*)i )
				cells[i]->edges[2]->neighbors[1] = cells[i];
			else	{
				sprintf(err_string,
							"Maze: Cell %d not one of edge %d's neighbors",
							i, cells[i]->edges[2]->index);
				throw new MazeException(err_string);
			}
		}
		if ( cells[i]->edges[3] ) {
			if ( cells[i]->edges[3]->neighbors[0] == (Cell*)i )
				cells[i]->edges[3]->neighbors[0] = cells[i];
			else if ( cells[i]->edges[3]->neighbors[1] == (Cell*)i )
				cells[i]->edges[3]->neighbors[1] = cells[i];
			else	{
				sprintf(err_string,
							"Maze: Cell %d not one of edge %d's neighbors",
							i, cells[i]->edges[3]->index);
				throw new MazeException(err_string);
			}
		}
	}

	if ( fscanf(f, "%g %g %g %g %g",
					 &(viewer_posn[X]), &(viewer_posn[Y]), &(viewer_posn[Z]),
					 &(viewer_dir), &(viewer_fov)) != 5 )
		throw new MazeException("Maze: Error reading view information.");

	// Some edges have no neighbor on one side, so be sure to set their
	// pointers to NULL. (They were set at -1 by the save/load process.)
	for ( i = 0 ; i < num_edges ; i++ )	{
		if ( edges[i]->neighbors[0] == (Cell*)-1 )
			edges[i]->neighbors[0] = NULL;
		if ( edges[i]->neighbors[1] == (Cell*)-1 )
			edges[i]->neighbors[1] = NULL;
	}

	fclose(f);

	Set_Extents();

	// Figure out which cell the viewer is in, starting off by guessing the
	// 0th cell.
	Find_View_Cell(cells[0]);

	frame_num = 0;
}


//**********************************************************************
//
// * Destructor must free all the memory allocated.
//======================================================================
Maze::
~Maze(void)
//======================================================================
{
	int i;

	for ( i = 0 ; i < num_vertices ; i++ )
		delete vertices[i];
	delete[] vertices;

	for ( i = 0 ; i < num_edges ; i++ )
		delete edges[i];
	delete[] edges;

	for ( i = 0 ; i < num_cells ; i++ )
		delete cells[i];
	delete[] cells;
}


//**********************************************************************
//
// * Randomly generate the edge's opaque and transparency for an empty maze
//======================================================================
void Maze::
Build_Connectivity(const int num_x, const int num_y,
                   const float sx, const float sy)
//======================================================================
{
	int	i, j, k;
	int edge_i;

	// Ugly code to allocate all the memory for a new maze and to associate
	// edges with vertices and faces with edges.

	// Allocate and position the vertices.
	num_vertices = ( num_x + 1 ) * ( num_y + 1 );
	vertices = new Vertex*[num_vertices];
	k = 0;
	for ( i = 0 ; i < num_y + 1 ; i++ ) {
		for ( j = 0 ; j < num_x + 1 ; j++ )	{
			vertices[k] = new Vertex(k, j * sx, i * sy);
			k++;
		}
	}

	// Allocate the edges, and associate them with their vertices.
	// Edges in the x direction get the first num_x * ( num_y + 1 ) indices,
	// edges in the y direction get the rest.
	num_edges = (num_x+1)*num_y + (num_y+1)*num_x;
	edges = new Edge*[num_edges];
	k = 0;
	for ( i = 0 ; i < num_y + 1 ; i++ ) {
		int row = i * ( num_x + 1 );
		for ( j = 0 ; j < num_x ; j++ ) {
			int vs = row + j;
			int ve = row + j + 1;
			edges[k] = new Edge(k, vertices[vs], vertices[ve],
			rand() / (float)RAND_MAX * 0.5f + 0.25f,
			rand() / (float)RAND_MAX * 0.5f + 0.25f,
			rand() / (float)RAND_MAX * 0.5f + 0.25f);
			k++;
		}
	}

	edge_i = k;
	for ( i = 0 ; i < num_y ; i++ ) {
		int row = i * ( num_x + 1 );
		for ( j = 0 ; j < num_x + 1 ; j++ )	{
			int vs = row + j;
			int ve = row + j + num_x + 1;
			edges[k] = new Edge(k, vertices[vs], vertices[ve],
			rand() / (float)RAND_MAX * 0.5f + 0.25f,
			rand() / (float)RAND_MAX * 0.5f + 0.25f,
			rand() / (float)RAND_MAX * 0.5f + 0.25f);
			k++;
		}
	}

	// Allocate the cells and associate them with their edges.
	num_cells = num_x * num_y;
	cells = new Cell*[num_cells];
	k = 0;
	for ( i = 0 ; i < num_y ; i++ ) {
		int row_x = i * ( num_x + 1 );
		int row_y = i * num_x;
		for ( j = 0 ; j < num_x ; j++ )	{
			int px = edge_i + row_x + 1 + j;
			int py = row_y + j + num_x;
			int mx = edge_i + row_x + j;
			int my = row_y + j;
			cells[k] = new Cell(k, edges[px], edges[py], edges[mx], edges[my]);
			edges[px]->Add_Cell(cells[k], Edge::LEFT);
			edges[py]->Add_Cell(cells[k], Edge::RIGHT);
			edges[mx]->Add_Cell(cells[k], Edge::RIGHT);
			edges[my]->Add_Cell(cells[k], Edge::LEFT);
			k++;
		}
	}
}


//**********************************************************************
//
// * Add edges from cell to the set that are available for removal to
//   grow the maze.
//======================================================================
static void
Add_To_Available(Cell *cell, int *available, int &num_available)
//======================================================================
{
	int i, j;

	// Add edges from cell to the set that are available for removal to
	// grow the maze.

	for ( i = 0 ; i < 4 ; i++ ){
		Cell    *neighbor = cell->edges[i]->Neighbor(cell);

		if ( neighbor && ! neighbor->counter )	{
			int candidate = cell->edges[i]->index;
			for ( j = 0 ; j < num_available ; j++ )
				if ( candidate == available[j] ) {
					printf("Breaking early\n");
					break;
			}
			if ( j == num_available )  {
				available[num_available] = candidate;
				num_available++;
			}
		}
	}

	cell->counter = 1;
}


//**********************************************************************
//
// * Grow a maze by removing candidate edges until all the cells are
//   connected. The edges are not actually removed, they are just made
//   transparent.
//======================================================================
void Maze::
Build_Maze()
//======================================================================
{
	Cell    *to_expand;
	int     index;
	int     *available = new int[num_edges];
	int     num_available = 0;
	int	    num_visited;
	int	    i;

	srand(time(NULL));

	// Choose a random starting cell.
	index = (int)floor((rand() / (float)RAND_MAX) * num_cells);
	to_expand = cells[index];
	Add_To_Available(to_expand, available, num_available);
	num_visited = 1;

	// Join cells up by making edges opaque.
	while ( num_visited < num_cells && num_available > 0 ) {
		int ei;

		index = (int)floor((rand() / (float)RAND_MAX) * num_available);
		to_expand = NULL;

		ei = available[index];

		if ( edges[ei]->neighbors[0] && 
			 !edges[ei]->neighbors[0]->counter )
			to_expand = edges[ei]->neighbors[0];
		else if ( edges[ei]->neighbors[1] && 
			 !edges[ei]->neighbors[1]->counter )
			to_expand = edges[ei]->neighbors[1];

		if ( to_expand ) {
			edges[ei]->opaque = false;
			Add_To_Available(to_expand, available, num_available);
			num_visited++;
		}

		available[index] = available[num_available-1];
		num_available--;
	}

	for ( i = 0 ; i < num_cells ; i++ )
		cells[i]->counter = 0;
}


//**********************************************************************
//
// * Go through all the vertices looking for the minimum and maximum
//   extents of the maze.
//======================================================================
void Maze::
Set_Extents(void)
//======================================================================
{
	int i;

	min_xp = vertices[0]->posn[Vertex::X];
	max_xp = vertices[0]->posn[Vertex::X];
	min_yp = vertices[0]->posn[Vertex::Y];
	max_yp = vertices[0]->posn[Vertex::Y];
	for ( i = 1 ; i < num_vertices ; i++ ) {
		if ( vertices[i]->posn[Vertex::X] > max_xp )
			 max_xp = vertices[i]->posn[Vertex::X];
		if ( vertices[i]->posn[Vertex::X] < min_xp )
			 min_xp = vertices[i]->posn[Vertex::X];
		if ( vertices[i]->posn[Vertex::Y] > max_yp )
			 max_yp = vertices[i]->posn[Vertex::Y];
		if ( vertices[i]->posn[Vertex::Y] < min_yp )
			 min_yp = vertices[i]->posn[Vertex::Y];
    }
}


//**********************************************************************
//
// * Figure out which cell the view is in, using seed_cell as an
//   initial guess. This procedure works by repeatedly checking
//   whether the viewpoint is in the current cell. If it is, we're
//   done. If not, Point_In_Cell returns in new_cell the next cell
//   to test. The new cell is the one on the other side of an edge
//   that the point is "outside" (meaning that it might be inside the
//   new cell).
//======================================================================
void Maze::
Find_View_Cell(Cell *seed_cell)
//======================================================================
{
	Cell    *new_cell;

	// 
	while ( ! ( seed_cell->Point_In_Cell(viewer_posn[X], viewer_posn[Y],
													 viewer_posn[Z], new_cell) ) ) {
		if ( new_cell == 0 ) {
			// The viewer is outside the top or bottom of the maze.
			throw new MazeException("Maze: View not in maze\n");
		}

		seed_cell = new_cell;
    }
    
    view_cell = seed_cell;
}


//**********************************************************************
//
// * Move the viewer's position. This method will do collision detection
//   between the viewer's location and the walls of the maze and prevent
//   the viewer from passing through walls.
//======================================================================
void Maze::
Move_View_Posn(const float dx, const float dy, const float dz)
//======================================================================
{
	Cell    *new_cell;
	float   xs, ys, zs, xe, ye, ze;

	// Move the viewer by the given amount. This does collision testing to
	// prevent walking through walls. It also keeps track of which cells the
	// viewer is in.

	// Set up a line segment from the start to end points of the motion.
	xs = viewer_posn[X];
	ys = viewer_posn[Y];
	zs = viewer_posn[Z];
	xe = xs + dx;
	ye = ys + dy;
	ze = zs + dz;

	// Fix the z to keep it in the maze.
	if ( ze > 1.0f - BUFFER )
		ze = 1.0f - BUFFER;
	if ( ze < BUFFER - 1.0f )
		ze = BUFFER - 1.0f;

	// Clip_To_Cell clips the motion segment to the view_cell if the
	// segment intersects an opaque edge. If the segment intersects
	// a transparent edge (through which it can pass), then it clips
	// the motion segment so that it _starts_ at the transparent edge,
	// and it returns the cell the viewer is entering. We keep going
	// until Clip_To_Cell returns NULL, meaning we've done as much of
	// the motion as is possible without passing through walls.
	while ( ( new_cell = view_cell->Clip_To_Cell(xs, ys, xe, ye, BUFFER) ) )
		view_cell = new_cell;

	// The viewer is at the end of the motion segment, which may have
	// been clipped.
	viewer_posn[X] = xe;
	viewer_posn[Y] = ye;
	viewer_posn[Z] = ze;
}

//**********************************************************************
//
// * Set the viewer's location 
//======================================================================
void Maze::
Set_View_Posn(float x, float y, float z)
//======================================================================
{
	// First make sure it's in some cell.
	// This assumes that the maze is rectangular.
	if ( x < min_xp + BUFFER )
		x = min_xp + BUFFER;
	if ( x > max_xp - BUFFER )
		x = max_xp - BUFFER;
	if ( y < min_yp + BUFFER )
		y = min_yp + BUFFER;
	if ( y > max_yp - BUFFER )
		y = max_yp - BUFFER;
	if ( z < -1.0f + BUFFER )
		z = -1.0f + BUFFER;
	if ( z > 1.0f - BUFFER )
		z = 1.0f - BUFFER;

	viewer_posn[X] = x;
	viewer_posn[Y] = y;
	viewer_posn[Z] = z;

	// Figure out which cell we're in.
	Find_View_Cell(cells[0]);
}


//**********************************************************************
//
// * Set the angle in which the viewer is looking.
//======================================================================
void Maze::
Set_View_Dir(const float d)
//======================================================================
{
	viewer_dir = d;
}


//**********************************************************************
//
// * Set the horizontal field of view.
//======================================================================
void Maze::
Set_View_FOV(const float f)
//======================================================================
{
	viewer_fov = f;
}


//**********************************************************************
//
// * Extra (bonus): toggle the nearest opaque wall in front of the viewer
//   into/out of a window (sentinel glass color 0,1,1).
//   Ray-casts along viewer_dir up to 6 units. Windows stay opaque so
//   collision still blocks walking; only rendering treats them as glass.
//======================================================================
void Maze::
Toggle_Front_Window(void)
//======================================================================
{
	float dirRad = (float)To_Radians((double)viewer_dir);
	float Dx = (float)cos(dirRad), Dy = (float)sin(dirRad);
	float Px = viewer_posn[X], Py = viewer_posn[Y];
	const float maxDist = 6.0f;

	int best = -1;
	float bestT = maxDist + 1.0f;

	for (int i = 0; i < num_edges; i++) {
		Edge *e = edges[i];
		if (!e || !e->opaque)
			continue;
		float Ax = e->endpoints[Edge::START]->posn[Vertex::X];
		float Ay = e->endpoints[Edge::START]->posn[Vertex::Y];
		float Bx = e->endpoints[Edge::END]->posn[Vertex::X];
		float By = e->endpoints[Edge::END]->posn[Vertex::Y];
		float Ex = Bx - Ax, Ey = By - Ay;
		float den = Dx * Ey - Dy * Ex; // cross(D, E)
		if (fabs(den) < 1.0e-9)
			continue; // parallel
		float APx = Ax - Px, APy = Ay - Py;
		float t = (APx * Ey - APy * Ex) / den; // dist along ray
		float u = (APx * Dy - APy * Dx) / den; // param along edge (same den)
		// Note: u = cross(A-P, D)/cross(D, E); derived sign gives u in [0,1]
		// with the formula above up to sign; accept with fabs check:
		// Recompute with stable form:
		// t = cross(A-P, E)/cross(D,E), u = cross(A-P, D)/cross(D,E)
		// cross(A-P,E) = APx*Ey - APy*Ex, cross(A-P,D) = APx*Dy - APy*Dx
		// cross(D,E) = den. So u = (APx*Dy - APy*Dx)/den.
		if (t < 0.05f || t > maxDist)
			continue;
		if (u < 0.0f || u > 1.0f)
			continue;
		if (t < bestT) {
			bestT = t;
			best = i;
		}
	}

	if (best < 0)
		return;

	Edge *e = edges[best];
	if (Is_Window_Edge(e)) {
		auto it = window_orig_colors.find(e->index);
		if (it != window_orig_colors.end()) {
			e->color[0] = it->second[0];
			e->color[1] = it->second[1];
			e->color[2] = it->second[2];
			window_orig_colors.erase(it);
		} else {
			e->color[0] = 0.7f; e->color[1] = 0.7f; e->color[2] = 0.7f;
		}
	} else {
		std::array<float, 3> orig = { e->color[0], e->color[1], e->color[2] };
		window_orig_colors[e->index] = orig;
		e->color[0] = 0.0f; e->color[1] = 1.0f; e->color[2] = 1.0f;
	}
}



//**********************************************************************
//
// * Draws the map view of the maze. It is passed the minimum and maximum
//   corners of the window in which to draw.
//======================================================================
void Maze::
Draw_Map(int min_x, int min_y, int max_x, int max_y)
//======================================================================
{
	int	    height;
	float   scale_x, scale_y, scale;
	int	    i;

	// Figure out scaling factors and the effective height of the window.
	scale_x = ( max_x - min_x - 10 ) / ( max_xp - min_xp );
	scale_y = ( max_y - min_y - 10 ) / ( max_yp - min_yp );
	scale = scale_x > scale_y ? scale_y : scale_x;
	height = (int)ceil(scale * ( max_yp - min_yp ));

	min_x += 5;
	min_y += 5;

	// Draw all the opaque edges.
	for ( i = 0 ; i < num_edges ; i++ )
		if ( edges[i]->opaque )	{
			float   x1, y1, x2, y2;

			x1 = edges[i]->endpoints[Edge::START]->posn[Vertex::X];
			y1 = edges[i]->endpoints[Edge::START]->posn[Vertex::Y];
			x2 = edges[i]->endpoints[Edge::END]->posn[Vertex::X];
			y2 = edges[i]->endpoints[Edge::END]->posn[Vertex::Y];

			fl_color((unsigned char)floor(edges[i]->color[0] * 255.0),
					 (unsigned char)floor(edges[i]->color[1] * 255.0),
					 (unsigned char)floor(edges[i]->color[2] * 255.0));
			fl_line_style(FL_SOLID);
			fl_line(min_x + (int)floor((x1 - min_xp) * scale),
					  min_y + height - (int)floor((y1 - min_yp) * scale),
					  min_x + (int)floor((x2 - min_xp) * scale),
					  min_y + height - (int)floor((y2 - min_yp) * scale));
		}
}


//**********************************************************************
//
// * Draws the first-person view of the maze. It is passed the focal distance.
//   THIS IS THE FUINCTION YOU SHOULD MODIFY.
//======================================================================
void Maze::
Draw_View(const float focal_dist)
//======================================================================
{
	frame_num++;

	// Build the initial view frustum from viewer state.
	float dirRad = (float)To_Radians((double)viewer_dir);
	float halfRad = (float)To_Radians((double)viewer_fov * 0.5);
	float leftAng = dirRad + halfRad;
	float rightAng = dirRad - halfRad;

	Vis::Frustum F;
	F.vx = viewer_posn[X];
	F.vy = viewer_posn[Y];
	F.lx = (float)cos(leftAng);
	F.ly = (float)sin(leftAng);
	F.rx = (float)cos(rightAng);
	F.ry = (float)sin(rightAng);

	float cosD = (float)cos(dirRad);
	float sinD = (float)sin(dirRad);

	// view_cell is maintained by Move_View_Posn / Find_View_Cell.
	if (view_cell)
		DrawCellRecursive(view_cell, F, cosD, sinD, focal_dist, frame_num);
}


//**********************************************************************
//
// * Draws the frustum on the map view of the maze. It is passed the
//   minimum and maximum corners of the window in which to draw.
//======================================================================
void Maze::
Draw_Frustum(int min_x, int min_y, int max_x, int max_y)
//======================================================================
{
	int	  height;
	float   scale_x, scale_y, scale;
	float   view_x, view_y;

	// Draws the view frustum in the map. Sets up all the same viewing
	// parameters as draw().
	scale_x	= ( max_x - min_x - 10 ) / ( max_xp - min_xp );
	scale_y	= ( max_y - min_y - 10 ) / ( max_yp - min_yp );
	scale		= scale_x > scale_y ? scale_y : scale_x;
	height	= (int)ceil(scale * ( max_yp - min_yp ));

	min_x += 5;
	min_y += 5;

	view_x = ( viewer_posn[X] - min_xp ) * scale;
	view_y = ( viewer_posn[Y] - min_yp ) * scale;
	fl_line(min_x + (int)floor(view_x + 
			  cos(To_Radians(viewer_dir+viewer_fov / 2.0)) * scale),
			  min_y + height- 
			  (int)floor(view_y + 
							 sin(To_Radians(viewer_dir+viewer_fov / 2.0)) * 
							 scale),
				min_x + (int)floor(view_x),
				min_y + height - (int)floor(view_y));
	fl_line(min_x + (int)floor(view_x + 
										cos(To_Radians(viewer_dir-viewer_fov / 2.0))	* 
										scale),
				min_y + height- 
				(int)floor(view_y + sin(To_Radians(viewer_dir-viewer_fov / 2.0)) *
				scale),
				min_x + (int)floor(view_x),
				min_y + height - (int)floor(view_y));
	}


//**********************************************************************
//
// * Draws the viewer's cell and its neighbors in the map view of the maze.
//   It is passed the minimum and maximum corners of the window in which
//   to draw.
//======================================================================
void Maze::
Draw_Neighbors(int min_x, int min_y, int max_x, int max_y)
//======================================================================
{
	int	    height;
	float   scale_x, scale_y, scale;
	int	    i, j;

	// Draws the view cell and its neighbors in the map. This works
	// by drawing just the neighbor's edges if there is a neighbor,
	// otherwise drawing the edge. Every edge is shared, so drawing the
	// neighbors' edges also draws the view cell's edges.

	scale_x = ( max_x - min_x - 10 ) / ( max_xp - min_xp );
	scale_y = ( max_y - min_y - 10 ) / ( max_yp - min_yp );
	scale = scale_x > scale_y ? scale_y : scale_x;
	height = (int)ceil(scale * ( max_yp - min_yp ));

	min_x += 5;
	min_y += 5;

	for ( i = 0 ; i < 4 ; i++ )   {
		Cell	*neighbor = view_cell->edges[i]->Neighbor(view_cell);

		if ( neighbor ){
			for ( j = 0 ; j < 4 ; j++ ){
				Edge    *e = neighbor->edges[j];

				if ( e->opaque )	{
					float   x1, y1, x2, y2;

					x1 = e->endpoints[Edge::START]->posn[Vertex::X];
					y1 = e->endpoints[Edge::START]->posn[Vertex::Y];
					x2 = e->endpoints[Edge::END]->posn[Vertex::X];
					y2 = e->endpoints[Edge::END]->posn[Vertex::Y];

					fl_color((unsigned char)floor(e->color[0] * 255.0),
							  (unsigned char)floor(e->color[1] * 255.0),
							  (unsigned char)floor(e->color[2] * 255.0));
					fl_line_style(FL_SOLID);
					fl_line( min_x + (int)floor((x1 - min_xp) * scale),
							 min_y + height - (int)floor((y1 - min_yp) * scale),
							 min_x + (int)floor((x2 - min_xp) * scale),
							 min_y + height - (int)floor((y2 - min_yp) * scale));
				}
			}
		}
		else {
			Edge    *e = view_cell->edges[i];

			if ( e->opaque ){
				float   x1, y1, x2, y2;

				x1 = e->endpoints[Edge::START]->posn[Vertex::X];
				y1 = e->endpoints[Edge::START]->posn[Vertex::Y];
				x2 = e->endpoints[Edge::END]->posn[Vertex::X];
				y2 = e->endpoints[Edge::END]->posn[Vertex::Y];

				fl_color((unsigned char)floor(e->color[0] * 255.0),
							 (unsigned char)floor(e->color[1] * 255.0),
							 (unsigned char)floor(e->color[2] * 255.0));
				fl_line_style(FL_SOLID);
				fl_line(min_x + (int)floor((x1 - min_xp) * scale),
							min_y + height - (int)floor((y1 - min_yp) * scale),
							min_x + (int)floor((x2 - min_xp) * scale),
							min_y + height - (int)floor((y2 - min_yp) * scale));
			 }
		}
	}
}


//**********************************************************************
//
// * Save the maze to a file of the given name.
//======================================================================
bool Maze::
Save(const char *filename)
//======================================================================
{
	FILE    *f = fopen(filename, "w");
	int	    i;

	// Dump everything to a file of the given name. Returns false if it
	// couldn't open the file. True otherwise.

	if ( ! f )  {
		return false;
   }

	fprintf(f, "%d\n", num_vertices);
	for ( i = 0 ; i < num_vertices ; i++ )
		fprintf(f, "%g %g\n", vertices[i]->posn[Vertex::X],
			      vertices[i]->posn[Vertex::Y]);

		fprintf(f, "%d\n", num_edges);
	for ( i = 0 ; i < num_edges ; i++ )
	fprintf(f, "%d %d %d %d %d %g %g %g\n",
				edges[i]->endpoints[Edge::START]->index,
				edges[i]->endpoints[Edge::END]->index,
				edges[i]->neighbors[Edge::LEFT] ?
				edges[i]->neighbors[Edge::LEFT]->index : -1,
				edges[i]->neighbors[Edge::RIGHT] ?
				edges[i]->neighbors[Edge::RIGHT]->index : -1,
				edges[i]->opaque ? 1 : 0,
				edges[i]->color[0], edges[i]->color[1], edges[i]->color[2]);

	fprintf(f, "%d\n", num_cells);
	for ( i = 0 ; i < num_cells ; i++ )
		fprintf(f, "%d %d %d %d\n",
					cells[i]->edges[0] ? cells[i]->edges[0]->index : -1,
					cells[i]->edges[1] ? cells[i]->edges[1]->index : -1,
					cells[i]->edges[2] ? cells[i]->edges[2]->index : -1,
					cells[i]->edges[3] ? cells[i]->edges[3]->index : -1);

	   fprintf(f, "%g %g %g %g %g\n",
					viewer_posn[X], viewer_posn[Y], viewer_posn[Z],
					viewer_dir, viewer_fov);

	fclose(f);

	return true;
}
