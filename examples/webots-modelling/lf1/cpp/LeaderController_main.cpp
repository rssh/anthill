// LeaderController main — Webots controller binary entry point.
//
// Glue between the Cyberbotics-reference inner-loop class
// (`MavicBase`, in mavic_base.{cpp,hpp}) and the anthill-generated
// outer-loop traits class (`anthill::examples::lf1::leader::LeaderController`).
//
// MavicBase exposes its own nested `Pose` / `Controls` POD types
// (protected members); the anthill side has parallel value types in
// `anthill::examples::lf1::leader`. This file marshals between them inside
// the subclass — free functions can't see MavicBase's protected
// nested types, so the conversions live as private static helpers.

#include "anthill_examples_lf1_leader.hpp"
#include "anthill_geometry.hpp"
#include "mavic_base.hpp"

#include <vector>

namespace {

namespace leader = anthill::examples::lf1::leader;
using anthill::geometry::Vec3;

leader::LeaderState initial_leader_state() {
    std::vector<leader::Waypoint> patrol{
        leader::Waypoint{ 5.0,  0.0},
        leader::Waypoint{ 0.0,  5.0},
        leader::Waypoint{-5.0,  0.0},
        leader::Waypoint{ 0.0, -5.0},
    };
    return leader::LeaderState{
        /* altitude_target = */ 5.0,
        /* precision       = */ 0.5,
        /* waypoints       = */ leader::WaypointSequence{patrol, 0},
    };
}

class LeaderImpl : public MavicBase {
public:
    LeaderImpl() : state_(initial_leader_state()) {}

protected:
    Controls computeControls(const Pose& pose) override {
        const leader::Pose anthill_pose = to_anthill(pose);
        state_ = leader::LeaderController::advance_waypoint(state_, anthill_pose);
        return to_inner(leader::LeaderController::compute_controls(state_, anthill_pose));
    }

private:
    // Conversions live inside the subclass so they can name MavicBase's
    // protected nested types (Pose / Controls).
    static leader::Pose to_anthill(const Pose& p) {
        return leader::Pose{
            Vec3{p.x, p.y, p.z},
            p.roll, p.pitch, p.yaw,
        };
    }

    static Controls to_inner(const leader::Controls& c) {
        Controls out;
        out.yaw = c.yaw;
        out.pitch = c.pitch;
        out.roll = c.roll;
        out.target_altitude = c.target_altitude;
        return out;
    }

    leader::LeaderState state_;
};

}  // anonymous namespace

int main() {
    LeaderImpl leader;
    leader.run();
    return 0;
}
