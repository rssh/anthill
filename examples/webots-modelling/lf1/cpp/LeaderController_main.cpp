// LeaderController main — Webots controller binary entry point.
//
// Glue between the Cyberbotics-reference inner-loop class
// (`MavicBase`, in mavic_base.{cpp,hpp}) and the anthill-generated
// outer-loop traits class (`anthill::examples::lf1::LeaderController`).
//
// MavicBase exposes its own nested `Pose` / `Controls` POD types
// (protected members); the anthill side has parallel value types in
// `anthill::examples::lf1`. This file marshals between them inside
// the subclass — free functions can't see MavicBase's protected
// nested types, so the conversions live as private static helpers.

#include "anthill_geometry.hpp"
#include "lf1.hpp"
#include "mavic_base.hpp"

#include <vector>

namespace {

namespace lf1 = anthill::examples::lf1;
using anthill::geometry::Vec3;

lf1::LeaderState initial_leader_state() {
    std::vector<lf1::Waypoint> patrol{
        lf1::Waypoint{ 5.0,  0.0},
        lf1::Waypoint{ 0.0,  5.0},
        lf1::Waypoint{-5.0,  0.0},
        lf1::Waypoint{ 0.0, -5.0},
    };
    return lf1::LeaderState{
        /* altitude_target = */ 5.0,
        /* precision       = */ 0.5,
        /* waypoints       = */ lf1::WaypointSequence{patrol, 0},
    };
}

class LeaderImpl : public MavicBase {
public:
    LeaderImpl() : state_(initial_leader_state()) {}

protected:
    Controls computeControls(const Pose& pose) override {
        const lf1::Pose anthill_pose = to_anthill(pose);
        state_ = lf1::LeaderController::advance_waypoint(state_, anthill_pose);
        return to_inner(lf1::LeaderController::compute_controls(state_, anthill_pose));
    }

private:
    // Conversions live inside the subclass so they can name MavicBase's
    // protected nested types (Pose / Controls).
    static lf1::Pose to_anthill(const Pose& p) {
        return lf1::Pose{
            Vec3{p.x, p.y, p.z},
            p.roll, p.pitch, p.yaw,
        };
    }

    static Controls to_inner(const lf1::Controls& c) {
        Controls out;
        out.yaw = c.yaw;
        out.pitch = c.pitch;
        out.roll = c.roll;
        out.target_altitude = c.target_altitude;
        return out;
    }

    lf1::LeaderState state_;
};

}  // anonymous namespace

int main() {
    LeaderImpl leader;
    leader.run();
    return 0;
}
