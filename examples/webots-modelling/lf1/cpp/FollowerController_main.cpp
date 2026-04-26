// FollowerController main — Webots controller binary entry point.
//
// Same shape as LeaderController_main.cpp: subclass MavicBase,
// override computeControls(), marshal to/from anthill types via
// private static helpers (MavicBase's nested Pose / Controls types
// are protected, so conversions can't be free functions).
//
// The world file launches *two* follower drones from this same
// binary, distinguished by a `--offset=x,y,z` argv passed via
// `controllerArgs` on the Webots Robot node.

#include "anthill_geometry.hpp"
#include "lf1.hpp"
#include "mavic_base.hpp"

#include <cstdio>
#include <cstdlib>
#include <cstring>

namespace {

namespace lf1 = anthill::examples::lf1;
using anthill::geometry::Vec3;

// Parse `--offset=x,y,z` from argv. Defaults to (-3, 1, 0) — a sane
// "follow behind and to starboard" position when no flag is given.
Vec3 parse_offset(int argc, char** argv) {
    Vec3 fallback{-3.0, 1.0, 0.0};
    for (int i = 1; i < argc; ++i) {
        const char* prefix = "--offset=";
        const std::size_t plen = std::strlen(prefix);
        if (std::strncmp(argv[i], prefix, plen) != 0) continue;
        Vec3 v{};
        if (std::sscanf(argv[i] + plen, "%lf,%lf,%lf", &v.x, &v.y, &v.z) == 3) {
            return v;
        }
    }
    return fallback;
}

lf1::FollowerState initial_follower_state(const Vec3& offset) {
    return lf1::FollowerState{
        offset,
        std::nullopt,
        /* hover_altitude = */ 5.0,
    };
}

class FollowerImpl : public MavicBase {
public:
    explicit FollowerImpl(Vec3 offset)
        : state_(initial_follower_state(offset)) {}

protected:
    Controls computeControls(const Pose& pose) override {
        // TODO: drain receiver packets, decode each into a Pose, and
        // call FollowerController::update_leader_pose. Once the
        // Receiver effect lowering is wired up the receiver handle
        // becomes a parameter to the override and this hook moves
        // back into the anthill spec.
        return to_inner(lf1::FollowerController::compute_controls(state_, to_anthill(pose)));
    }

private:
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

    lf1::FollowerState state_;
};

}  // anonymous namespace

int main(int argc, char** argv) {
    const Vec3 offset = parse_offset(argc, argv);
    FollowerImpl follower(offset);
    follower.run();
    return 0;
}
