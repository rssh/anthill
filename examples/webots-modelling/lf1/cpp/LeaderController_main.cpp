// LeaderController main — Webots controller binary entry point.
//
// Hand-authored. Glues anthill's pure outer-loop functions
// (`anthill::examples::lf1::LeaderController::*`) into the mutable
// state machine MavicBase expects. Anthill produces the static
// methods; this file holds the per-instance state and wires the
// two together via the standard "subclass MavicBase, override
// compute_controls" pattern.

#include "lf1.hpp"
#include "mavic_base.hpp"

#include <vector>

namespace {

using anthill::examples::lf1::Controls;
using anthill::examples::lf1::LeaderController;
using anthill::examples::lf1::LeaderState;
using anthill::examples::lf1::Pose;
using anthill::examples::lf1::Waypoint;
using anthill::examples::lf1::WaypointSequence;

// Hard-coded patrol pattern matching the Cyberbotics reference's
// leader waypoints. In a real deployment these come from the world
// file; for the v0 controller we hard-code a square pattern.
LeaderState initial_leader_state() {
    std::vector<Waypoint> patrol{
        Waypoint{ 5.0,  0.0},
        Waypoint{ 0.0,  5.0},
        Waypoint{-5.0,  0.0},
        Waypoint{ 0.0, -5.0},
    };
    return LeaderState{
        /* altitude_target = */ 5.0,
        /* precision       = */ 0.5,
        /* waypoints       = */ WaypointSequence{patrol, 0},
    };
}

class LeaderImpl : public anthill::lf1::runtime::MavicBase {
public:
    explicit LeaderImpl(int basic_time_step_ms)
        : MavicBase(basic_time_step_ms),
          state_(initial_leader_state()) {}

protected:
    Controls compute_controls(const Pose& pose) override {
        // Outer-loop dance: advance the waypoint cursor when within
        // precision, then compute heading + thrust controls. Both
        // are pure functions — anthill produces them; we hold the
        // state.
        state_ = LeaderController::advance_waypoint(state_, pose);
        return LeaderController::compute_controls(state_, pose);
    }

private:
    LeaderState state_;
};

}  // anonymous namespace

int main() {
    constexpr int kBasicTimeStepMs = 32;
    LeaderImpl leader(kBasicTimeStepMs);
    leader.run();
    return 0;
}
