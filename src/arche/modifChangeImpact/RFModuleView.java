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
 * A simple design view for modifiability analysis (based on the module viewtype)
 * 
 * @author Andres Diaz-Pace
 */

import java.util.List;

import arche.modifChangeImpact.hibernate.vo.ArchEModuleVO;

import edu.cmu.sei.arche.external.data.ArchEResponsibility;
import edu.cmu.sei.arche.external.data.ArchEView;

public interface RFModuleView extends ArchEView {

	/** 
	 * It checks if a responsibility is allocated to some existing module
	 * 
	 * @param responsibility
	 * @return
	 */	
	public boolean isAllocated(ArchEResponsibility responsibility);

	/** 
	 * It checks if a responsibility is allocated to a given module
	 * 
	 * @param responsibility
	 * @param module
	 * @return
	 */
	public boolean isAllocated(ArchEResponsibility responsibility, ArchEModuleVO module);
	
	/** 
	 * It checks if two existing responsibilities are allocated to the same module
	 * 
	 * @param module
	 * @param resp1
	 * @param resp2
	 * @return
	 */
	public boolean areCoAllocated(ArchEModuleVO module, ArchEResponsibility resp1, ArchEResponsibility resp2);
	
	/** 
	 * It checks if two existing responsibilities are allocated to some shared module
	 * 
	 * @param resp1
	 * @param resp2
	 * @return
	 */
	public boolean areCoAllocated(ArchEResponsibility resp1, ArchEResponsibility resp2);

	/** 
	 * It checks if a dependency exists between two existing modules
	 * 
	 * @param module1
	 * @param module2
	 * @return
	 */
	public boolean hasDependency(ArchEModuleVO module1, ArchEModuleVO module2);	

	/** 
	 * It returns all the modules defined for this view that contain a specific responsibility
	 * 
	 * @param responsibility
	 * @return
	 */
	public List<ArchEModuleVO> getModulesByResponsibility(ArchEResponsibility responsibility);
	
	/** 
	 * It returns all the modules defined for this view
	 * 
	 * @return
	 */ 
	public List<ArchEModuleVO> getModules();
	
	/** 
	 * It returns all the responsibilities allocated to a particular module in this view
	 * 
	 * @param module
	 * @return
	 */
	public List<ArchEResponsibility> getResponsibilitiesByModule(ArchEModuleVO module);


}

