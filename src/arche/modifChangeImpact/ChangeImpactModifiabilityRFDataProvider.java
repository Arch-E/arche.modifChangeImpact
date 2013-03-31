/*
 * ArchE
 * Copyright (c) 2012 Carnegie Mellon University.
 * All Rights Reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following acknowledgments and disclaimers.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. All advertising materials for third-party software mentioning features or
 * use of this software must display the following disclaimer:
 *
 * “Neither Carnegie Mellon University nor its Software Engineering Institute
 * have reviewed or endorsed this software”
 *
 * 4. The names “Carnegie Mellon University,” and/or “Software Engineering
 * Institute" shall not be used to endorse or promote products derived from
 * this software without prior written permission. For written permission,
 * please contact permission@sei.cmu.edu.
 *
 * 5. Redistributions of any form whatsoever must retain the following
 * acknowledgment:
 *
 * Copyright 2012 Carnegie Mellon University.
 *
 * This material is based upon work funded and supported by the United States
 * Department of Defense under Contract No. FA8721-05-C-0003 with Carnegie
 * Mellon University for the operation of the Software Engineering Institute, a
 * federally funded research and development center.
 *
 * NO WARRANTY
 *
 * THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING INSTITUTE MATERIAL
 * IS FURNISHED ON AN “AS-IS” BASIS. CARNEGIE MELLON UNIVERSITY MAKES NO
 * WARRANTIES OF ANY KIND, EITHER EXPRESSED OR IMPLIED, AS TO ANY MATTER
 * INCLUDING, BUT NOT LIMITED TO, WARRANTY OF FITNESS FOR PURPOSE OR
 * MERCHANTABILITY, EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF THE MATERIAL.
 * CARNEGIE MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF ANY KIND WITH
 * RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT INFRINGEMENT.
 */

package arche.modifChangeImpact;

/**
 * A class for managing data for the modifiability reasoning framework (e.g.,
 * responsibility structure, module view, etc.)
 * 
 * @author Hyunwoo Kim
 */

import edu.cmu.sei.arche.ArchEException;

import arche.modifChangeImpact.hibernate.ArchECoreArchitecture;
import arche.modifChangeImpact.hibernate.ArchECoreDataProvider;
import arche.modifChangeImpact.hibernate.ArchECoreRequirementModel;
import arche.modifChangeImpact.hibernate.ArchECoreResponsibilityStructure;
import arche.modifChangeImpact.hibernate.ArchECoreView;
import arche.modifChangeImpact.hibernate.vo.ArchEVersionVO;


public class ChangeImpactModifiabilityRFDataProvider extends ArchECoreDataProvider {
	
	@Override
	public ArchECoreArchitecture newArchitecture(ArchEVersionVO version)
			throws ArchEException { // The default architecture is used
		return new ArchECoreArchitecture(version); 
	}

	@Override
	public ArchECoreRequirementModel newRequirementModel(ArchEVersionVO version)
			throws ArchEException { // The default requirement model (scenarios) is used
		return new ArchECoreRequirementModel(version);
	}

	@Override
	public ArchECoreResponsibilityStructure newResponsibilityStructure(
			ArchECoreArchitecture architecture) throws ArchEException {
		// A custom responsibility structure is defined (for responsibility dependencies
		// and modifiability-specific parameters)
		return new ChangeImpactModifiabilityResponsibilityStructure(architecture);
	}

	@Override
	public ArchECoreView newView(ArchECoreArchitecture architecture)
			throws ArchEException {
		// A custom architectural view is defined, which consists of modules, 
		// module dependencies and responsibility allocations
		return new ModuleADLWrapper(architecture);
	}
	
}

